package game

import (
	"encoding/json"
	"fmt"
	NameGenerator "github.com/Ahmadrezadl/funny-name-generator"
	"log"
	"math"
	"math/rand"
	"sort"
	"strings"
	"sync"
	"time"
	"unicode/utf8"

	discordemojimap "github.com/Bios-Marcel/discordemojimap/v2"
	"github.com/gofrs/uuid"
	"github.com/kennygrant/sanitize"
	"golang.org/x/text/cases"
	"golang.org/x/text/language"
)

var (
	LobbySettingBounds = &SettingBounds{
		MinDrawingTime:       3,  // SpyDrawer: per-turn timing (3-15 seconds)
		MaxDrawingTime:       15, // SpyDrawer: per-turn timing (3-15 seconds)
		MinRounds:            1,
		MaxRounds:            20,
		MinMaxPlayers:        2,
		MaxMaxPlayers:        24,
		MinClientsPerIPLimit: 1,
		WordsPerRound: 3,
		MaxClientsPerIPLimit: 24,
		MinWordsPerRound:     1,
		MaxWordsPerRound:     5,
	}
	SupportedLanguages = map[string]string{
		"words-fa": "کلمات فارسی",
		"words-en": "کلمات انگلیسی",
		"famous-fa": "شخصیت های معروف ایرانی",
		"friends":    "سریال Friends (انگلیسی)",
		"dota2":    "بازی Dota2 (انگلیسی)",
	}
)

const (
	DrawingBoardBaseWidth  = 1280
	DrawingBoardBaseHeight = 720
	MinBrushSize           = 8
	MaxBrushSize           = 32

	// SpyDrawer constants
	TurnDurationSeconds = 7 // Each turn is 15 seconds
	TurnsPerPlayer      = 3  // Each player draws 3 turns
	DefaultVoteDuration = 15 // Default voting duration in seconds
)

// SettingBounds defines the lower and upper bounds for the user-specified
// lobby creation input.
type SettingBounds struct {
	MinDrawingTime       int64 `json:"minDrawingTime"`
	MaxDrawingTime       int64 `json:"maxDrawingTime"`
	MinRounds            int64 `json:"minRounds"`
	MaxRounds            int64 `json:"maxRounds"`
	MinMaxPlayers        int64 `json:"minMaxPlayers"`
	MaxMaxPlayers        int64 `json:"maxMaxPlayers"`
	MinClientsPerIPLimit int64 `json:"minClientsPerIpLimit"`
	MaxClientsPerIPLimit int64 `json:"maxClientsPerIpLimit"`
	MinWordsPerRound     int64 `json:"minWordsPerRound"`
	MaxWordsPerRound     int64 `json:"maxWordsPerRound"`
	WordsPerRound        int64 `json:"wordsPerRound"`
}

// LineEvent is basically the same as GameEvent, but with a specific Data type.
// We use this for reparsing as soon as we know that the type is right. It's
// a bit unperformant, but will do for now.
type LineEvent struct {
	Type string `json:"type"`
	Data *Line  `json:"data"`
}

// FillEvent is basically the same as GameEvent, but with a specific Data type.
// We use this for reparsing as soon as we know that the type is right. It's
// a bit unperformant, but will do for now.
type FillEvent struct {
	Type string `json:"type"`
	Data *Fill  `json:"data"`
}

type SaveEvent struct {
	Type string `json:"type"`
}

// KickVote represents a players vote to kick another players. If the VoteCount
// is as great or greater than the RequiredVoteCount, the event indicates a
// successful kick vote. The voting is anonymous, meaning the voting player
// won't be exposed.
type KickVote struct {
	PlayerID          string `json:"playerId"`
	PlayerName        string `json:"playerName"`
	VoteCount         int    `json:"voteCount"`
	RequiredVoteCount int    `json:"requiredVoteCount"`
}

func (lobby *Lobby) HandleEvent(raw []byte, received *GameEvent, player *Player) error {
	lobby.mutex.Lock()
	defer lobby.mutex.Unlock()

	if received.Type == "message" {
		dataAsString, isString := (received.Data).(string)
		if !isString {
			return fmt.Errorf("invalid data received: '%s'", received.Data)
		}

		handleMessage(dataAsString, player, lobby)
	} else if received.Type == "line" {
		if lobby.canDraw(player) {
			line := &LineEvent{}
			jsonError := json.Unmarshal(raw, line)
			if jsonError != nil {
				return fmt.Errorf("error decoding data: %s", jsonError)
			}

			//In case the line is too big, we overwrite the data of the event.
			//This will prevent clients from lagging due to too thick lines.
			if line.Data.LineWidth > float32(MaxBrushSize) {
				line.Data.LineWidth = MaxBrushSize
				received.Data = line.Data
			} else if line.Data.LineWidth < float32(MinBrushSize) {
				line.Data.LineWidth = MinBrushSize
				received.Data = line.Data
			}

			// Override color with player's assigned color
			line.Data.Color = player.Color
			received.Data = line.Data

			lobby.AppendLine(line)

			//We directly forward the event, as it seems to be valid.
			lobby.sendDataToEveryoneExceptSender(player, received)
		}
	} else if received.Type == "save" {
		if lobby.canDraw(player) {
			lobby.saveState()
			lobby.sendDataToEveryoneExceptSender(player,GameEvent{Type:"save"})
		}
	} else if received.Type == "undo" {
		if lobby.canDraw(player) {
			lobby.undo()
			// Send undo to everyone including the sender (drawer) so they can see the undo too
			lobby.TriggerUpdateEvent("undo", nil)
		}
	} else if received.Type == "fill" {
		if lobby.canDraw(player) {
			fill := &FillEvent{}
			jsonError := json.Unmarshal(raw, fill)
			if jsonError != nil {
				return fmt.Errorf("error decoding data: %s", jsonError)
			}
			// Override color with player's assigned color
			fill.Data.Color = player.Color
			received.Data = fill.Data
			lobby.AppendFill(fill)

			//We directly forward the event, as it seems to be valid.
			lobby.sendDataToEveryoneExceptSender(player, received)
		}
	} else if received.Type == "clear-drawing-board" {
		if lobby.canDraw(player) && len(lobby.currentDrawing) > 0 {
			lobby.ClearDrawing()
			lobby.sendDataToEveryoneExceptSender(player, received)
		}
	} else if received.Type == "choose-word" {
		chosenIndex, isInt := (received.Data).(int)
		if !isInt {
			asFloat, isFloat32 := (received.Data).(float64)
			if isFloat32 && asFloat < 4 {
				chosenIndex = int(asFloat)
			} else {
				return fmt.Errorf("invalid data in choose-word event: %v", received.Data)
			}
		}

		drawer := lobby.drawer
		if player == drawer && len(lobby.wordChoice) > 0 && chosenIndex >= 0 && chosenIndex <= 4 {
			lobby.CurrentWord = lobby.wordChoice[chosenIndex]

			//Depending on how long the word is, a fixed amount of hints
			//would be too easy or too hard.
			runeCount := utf8.RuneCountInString(lobby.CurrentWord)
			if runeCount <= 2 {
				lobby.hintCount = 0
			} else if runeCount <= 4 {
				lobby.hintCount = 1
			} else if runeCount <= 9 {
				lobby.hintCount = 2
			} else {
				lobby.hintCount = 3
			}
			lobby.hintsLeft = lobby.hintCount

			lobby.wordChoice = nil
			lobby.wordHints = createWordHintFor(lobby.CurrentWord, false)
			lobby.wordHintsShown = createWordHintFor(lobby.CurrentWord, true)
			lobby.triggerWordHintUpdate()
		}
	} else if received.Type == "kick-vote" {
		if lobby.EnableVotekick {
			toKickID, isString := (received.Data).(string)
			if !isString {
				return fmt.Errorf("invalid data in kick-vote event: %v", received.Data)
			}

			handleKickVoteEvent(lobby, player, toKickID)
		}
	} else if received.Type == "start" {
		if lobby.Round == 0 && player == lobby.Owner {
			//We are reseting each players score, since players could
			//technically be player a second game after the last one
			//has already ended.
			for _, otherPlayer := range lobby.players {
				otherPlayer.Score = 0
				otherPlayer.LastScore = 0
				//Since nobody has any points in the beginning, everyone has practically
				//the same rank, therefore y'll winners for now.
				otherPlayer.Rank = 1
			}

			advanceLobby(lobby)
		}
	} else if received.Type == "name-change" {
		newName, isString := (received.Data).(string)
		if !isString {
			return fmt.Errorf("invalid data in name-change event: %v", received.Data)
		}
		handleNameChangeEvent(player, lobby, newName)
	} else if received.Type == "request-drawing" {
		lobby.WriteJSON(player, GameEvent{Type: "drawing", Data: lobby.currentDrawing})
	} else if received.Type == "vote" {
		if lobby.State == Voting {
			// SpyDrawer: Check if player joined mid-round (not in drawing order)
			joinedMidRound := false
			if lobby.Round > 0 {
				inDrawingOrder := false
				for _, p := range lobby.drawingOrder {
					if p == player {
						inDrawingOrder = true
						break
					}
				}
				joinedMidRound = !inDrawingOrder
			}
			
			if joinedMidRound {
				return fmt.Errorf("player joined mid-round and cannot vote")
			}
			
			votedForID, isString := (received.Data).(string)
			if !isString {
				return fmt.Errorf("invalid data in vote event: %v", received.Data)
			}
			handleVoteEvent(lobby, player, votedForID)
		}
	}
	/* else if received.Type == "keep-alive" {
		This is a known dummy event in order to avoid accidental websocket
		connection closure. However, no action is required on the server.
	}*/

	return nil
}

func handleMessage(message string, sender *Player, lobby *Lobby) {
	trimmedMessage := strings.TrimSpace(message)
	if trimmedMessage == "" {
		return
	}

	// In SpyDrawer, messages are just chat - no word guessing
	sendMessageToAll(trimmedMessage, sender, lobby)
}

func calculateGuesserScore(wordLength, secondsLeft, drawingTime int) int {
	// This function is no longer used in SpyDrawer (removed word guessing)
	// Keeping for test compatibility
	return 0
}

func (lobby *Lobby) isAnyoneStillGuessing() bool {
	for _, otherPlayer := range lobby.players {
		if otherPlayer.State == Guessing && otherPlayer.Connected {
			return true
		}
	}

	return false
}

func sendMessageToAll(message string, sender *Player, lobby *Lobby) {
	messageEvent := GameEvent{Type: "message", Data: Message{
		Author:   sender.Name,
		AuthorID: sender.ID,
		Content:  discordemojimap.Replace(message),
	}}
	for _, target := range lobby.players {
		lobby.WriteJSON(target, messageEvent)
	}
}

func (lobby *Lobby) sendMessageToAllNonGuessing(message string, sender *Player) {
	messageEvent := GameEvent{Type: "non-guessing-player-message", Data: Message{
		Author:   sender.Name,
		AuthorID: sender.ID,
		Content:  discordemojimap.Replace(message),
	}}
	for _, target := range lobby.players {
		if target.State != Guessing {
			lobby.WriteJSON(target, messageEvent)
		}
	}
}

func handleKickVoteEvent(lobby *Lobby, player *Player, toKickID string) {
	//Kicking yourself isn't allowed
	if toKickID == player.ID {
		return
	}

	//A player can't vote twice to kick someone
	if player.votedForKick[toKickID] {
		return
	}

	playerToKickIndex := -1
	for index, otherPlayer := range lobby.players {
		if otherPlayer.ID == toKickID {
			playerToKickIndex = index
			break
		}
	}

	//If we haven't found the player, we can't kick them.
	if playerToKickIndex == -1 {
		return
	}

	playerToKick := lobby.players[playerToKickIndex]

	player.votedForKick[toKickID] = true
	var voteKickCount int
	for _, otherPlayer := range lobby.players {
		if otherPlayer.Connected && otherPlayer.votedForKick[toKickID] {
			voteKickCount++
		}
	}

	votesRequired := calculateVotesNeededToKick(playerToKick, lobby)

	kickEvent := &GameEvent{
		Type: "kick-vote",
		Data: &KickVote{
			PlayerID:          playerToKick.ID,
			PlayerName:        playerToKick.Name,
			VoteCount:         voteKickCount,
			RequiredVoteCount: votesRequired,
		},
	}

	//We send the kick event to all players, since it was a valid vote.
	for _, otherPlayer := range lobby.players {
		lobby.WriteJSON(otherPlayer, kickEvent)
	}

	//If the valid vote also happens to be the last vote needed, we kick the player.
	//Since we send the events to all players beforehand, the target player is automatically
	//being noteified of his own kick.
	if voteKickCount >= votesRequired {
		kickPlayer(lobby, playerToKick, playerToKickIndex)
	}
}

// kickPlayer kicks the given player from the lobby, updating the lobby
// state and sending all necessary events.
func kickPlayer(lobby *Lobby, playerToKick *Player, playerToKickIndex int) {
	//Avoiding nilpointer in case playerToKick disconnects during this event unluckily.
	playerToKickSocket := playerToKick.ws
	if playerToKickSocket != nil {
		disconnectError := playerToKickSocket.Close()
		if disconnectError != nil {
			log.Printf("Error disconnecting kicked player:\n\t%s\n", disconnectError)
		}
	}

	//Since the player is already kicked, we first clean up the kicking information related to that player
	for _, otherPlayer := range lobby.players {
		delete(otherPlayer.votedForKick, playerToKick.ID)
	}

	lobby.players = append(lobby.players[:playerToKickIndex], lobby.players[playerToKickIndex+1:]...)

	if lobby.drawer == playerToKick {
		lobby.TriggerUpdateEvent("drawer-kicked", nil)
		//Since the drawing person has been kicked, that probably means that he/she was trolling, therefore
		//we redact everyones last earned score.
		for _, otherPlayer := range lobby.players {
			otherPlayer.Score -= otherPlayer.LastScore
			otherPlayer.LastScore = 0
		}
		lobby.scoreEarnedByGuessers = 0
		//We must absolutely not set lobby.drawer to nil, since this would cause the drawing order to be ruined.
	}

	//If the owner is kicked, we choose the next best person as the owner.
	if lobby.Owner == playerToKick {
		for _, otherPlayer := range lobby.players {
			potentialOwner := otherPlayer
			if potentialOwner.Connected {
				lobby.Owner = potentialOwner
				lobby.TriggerUpdateEvent("owner-change", &OwnerChangeEvent{
					PlayerID:   potentialOwner.ID,
					PlayerName: potentialOwner.Name,
				})
				break
			}
		}
	}

	if lobby.drawer == playerToKick || !lobby.isAnyoneStillGuessing() {
		advanceLobby(lobby)
	} else {
		//This isn't necessary in case we need to advanced the lobby, as it has
		//to happen anyways and sending events twice would be wasteful.
		recalculateRanks(lobby)
		lobby.triggerPlayersUpdate()
	}
}

type OwnerChangeEvent struct {
	PlayerID   string `json:"playerId"`
	PlayerName string `json:"playerName"`
}

type NameChangeEvent struct {
	PlayerID   string `json:"playerId"`
	PlayerName string `json:"playerName"`
}

func calculateVotesNeededToKick(playerToKick *Player, lobby *Lobby) int {
	connectedPlayerCount := lobby.GetConnectedPlayerCount()

	//If there are only two players, e.g. none of them should be able to
	//kick the other.
	if connectedPlayerCount <= 2 {
		return 2
	}

	if playerToKick == lobby.creator {
		//We don't want to allow people to kick the creator, as this could
		//potentially annoy certain creators. For example a streamer playing
		//a game with viewers could get trolled this way. Just one
		//hypothetical scenario, I am sure there are more ;)

		//All players excluding the owner themselves.
		return connectedPlayerCount - 1
	}

	//If the amount of players equals an even number, such as 6, we will always
	//need half of that. If the amount is uneven, we'll get a floored result.
	//therefore we always add one to the amount.
	//examples:
	//    (6+1)/2 = 3
	//    (5+1)/2 = 3
	//Therefore it'll never be possible for a minority to kick a player.
	return (connectedPlayerCount + 1) / 2
}

func handleNameChangeEvent(caller *Player, lobby *Lobby, name string) {
	oldName := caller.Name
	newName := SanitizeName(name)

	log.Printf("%s is now %s\n", oldName, newName)

	//We'll avoid sending the event in this case, as it's useless, but still log
	//the event, as it might be useful to know that this happened.
	if oldName != newName {
		caller.Name = newName
		lobby.TriggerUpdateEvent("name-change", &NameChangeEvent{
			PlayerID:   caller.ID,
			PlayerName: newName,
		})
	}
}

// advanceLobby handles the SpyDrawer game flow:
// - New round: assign spies, colors, word, start drawing turns
// - Next turn: move to next player's turn (or next turn of same player)
// - After all turns: enter voting phase
// - After voting: calculate scores and move to next round
func advanceLobby(lobby *Lobby) {
	if lobby.timeLeftTicker != nil {
		lobby.timeLeftTicker.Stop()
		lobby.timeLeftTicker = nil
	}

	// If we're in voting phase and all votes are in, we already calculated scores
	// Now move to next round
	if lobby.State == Voting {
		// Notify all players that voting has ended
		lobby.TriggerUpdateEvent("voting-end", map[string]interface{}{
			"players": lobby.players,
		})

		// Reset for next round
		lobby.votes = make(map[string]string)
		for _, player := range lobby.players {
			player.VoteTarget = ""
			player.LastScore = 0
		}

		// Check if game is over
		if lobby.Round >= lobby.Rounds {
			endGame(lobby)
			return
		}

		// Start new round
		lobby.Round++
		startNewRound(lobby)
		return
	}

	// If we're in the middle of drawing turns
	if lobby.State == Ongoing && len(lobby.drawingOrder) > 0 {
		// Round-robin: move to next player after each turn
		lobby.currentPlayerIndex++
		
		// Wrap around if we've gone through all players
		if lobby.currentPlayerIndex >= len(lobby.drawingOrder) {
			lobby.currentPlayerIndex = 0
			lobby.currentTurnNumber++
			
			// Check if we've completed all turns (3 turns per round)
			if lobby.currentTurnNumber > TurnsPerPlayer {
				// All drawing is done, enter voting phase
				startVotingPhase(lobby)
				return
			}
		}

		// Continue with next turn
		startNextDrawingTurn(lobby)
		return
	}

	// Starting the game or a new round
	startNewRound(lobby)
}

// startNewRound initializes a new round: assigns spies, colors, word, and starts drawing
func startNewRound(lobby *Lobby) {
	// Get connected players
	connectedPlayers := make([]*Player, 0)
	for _, player := range lobby.players {
		if player.Connected {
			connectedPlayers = append(connectedPlayers, player)
		}
	}

	if len(connectedPlayers) < 2 {
		return
	}

	// Assign colors to players
	assignColors(lobby)

	// Assign spies
	assignSpies(lobby)

	// Get a word for this round
	words := GetRandomWords(1, lobby)
	if len(words) == 0 {
		return
	}
	lobby.CurrentWord = words[0]
	// SpyDrawer: word-container is driven by word hints:
	// - non-spies see the full word
	// - spies see only the letter count (underscores)
	lobby.wordHintsShown = createWordHintFor(lobby.CurrentWord, true)
	lobby.wordHints = createWordHintFor(lobby.CurrentWord, false)

	// Set up drawing order (shuffle players)
	lobby.drawingOrder = make([]*Player, len(connectedPlayers))
	copy(lobby.drawingOrder, connectedPlayers)
	rand.Shuffle(len(lobby.drawingOrder), func(i, j int) {
		lobby.drawingOrder[i], lobby.drawingOrder[j] = lobby.drawingOrder[j], lobby.drawingOrder[i]
	})

	// Reset turn tracking
	lobby.currentPlayerIndex = 0
	lobby.currentTurnNumber = 1
	lobby.State = Ongoing
	lobby.ClearDrawing()

	// Send round-start to everyone
	wordLength := len([]rune(lobby.CurrentWord)) // Count runes for proper Unicode support
	for _, player := range connectedPlayers {
		lobby.WriteJSON(player, GameEvent{
			Type: "round-start",
			Data: map[string]interface{}{
				"word":       lobby.CurrentWord,
				"wordLength": wordLength,
				"isSpy":      player.IsSpy,
				"round":      lobby.Round,
				"players":    lobby.players,
			},
		})
	}

	// Push word-hints immediately so clients fill the word-container reliably (including mid-round joins).
	lobby.triggerWordHintUpdate()

	recalculateRanks(lobby)
	startNextDrawingTurn(lobby)
}

// startNextDrawingTurn starts the next 15-second drawing turn
func startNextDrawingTurn(lobby *Lobby) {
	if lobby.currentPlayerIndex >= len(lobby.drawingOrder) {
		return
	}

	currentDrawer := lobby.drawingOrder[lobby.currentPlayerIndex]
	lobby.drawer = currentDrawer
	currentDrawer.State = Drawing

	// Set all other ROUND participants to watching state.
	// Players that joined mid-round remain spectators.
	for _, player := range lobby.players {
		if !player.Connected || player == currentDrawer {
			continue
		}
		inOrder := false
		for _, p := range lobby.drawingOrder {
			if p == player {
				inOrder = true
				break
			}
		}
		if inOrder {
			player.State = Guessing
		} else {
			player.State = Spectator
		}
	}

	// Set timer using the lobby's DrawingTime setting (per-turn duration)
	turnDuration := lobby.DrawingTime
	if turnDuration <= 0 {
		turnDuration = TurnDurationSeconds // Fallback to default if not set
	}
	lobby.RoundEndTime = time.Now().UTC().UnixNano()/1000000 + int64(turnDuration)*1000
	lobby.timeLeftTicker = time.NewTicker(1 * time.Second)
	go startTurnTimeTicker(lobby)

	// Send personalized turn start notification
	for _, player := range lobby.players {
		if !player.Connected {
			continue
		}
		
		var message string
		if player == currentDrawer {
			if player.IsSpy {
				message = "شما جاسوس هستید! بدون دانستن کلمه نقاشی کنید."
			} else {
				message = fmt.Sprintf("کلمه شما: %s", lobby.CurrentWord)
			}
		} else {
			if player.IsSpy {
				message = fmt.Sprintf("شما جاسوس هستید! %s در حال نقاشی است.", currentDrawer.Name)
			} else {
				message = fmt.Sprintf("%s در حال نقاشی است. کلمه: %s", currentDrawer.Name, lobby.CurrentWord)
			}
		}
		
		lobby.WriteJSON(player, GameEvent{
			Type: "turn-toast",
			Data: map[string]interface{}{
				"message": message,
				"isYourTurn": player == currentDrawer,
			},
		})
	}

	// Notify all players
	lobby.TriggerUpdateEvent("drawing-turn", map[string]interface{}{
		"drawer":         currentDrawer.ID,
		"turnNumber":     lobby.currentTurnNumber,
		"playerTurn":     lobby.currentPlayerIndex + 1,
		"totalPlayers":   len(lobby.drawingOrder),
		"roundEndTime":   int(lobby.RoundEndTime - getTimeAsMillis()),
		"players":        lobby.players,
		"currentWord":     lobby.CurrentWord,
		"wordLength":     len([]rune(lobby.CurrentWord)),
	})
	// Keep word-container in sync even if a client missed round-start.
	lobby.triggerWordHintUpdate()
}

// startVotingPhase enters the voting phase where players guess the spy
func startVotingPhase(lobby *Lobby) {
	lobby.State = Voting
	lobby.drawer = nil
	lobby.votes = make(map[string]string)

	// Reset participant states (spectators can't vote)
	for _, player := range lobby.players {
		if !player.Connected {
			continue
		}
		inOrder := false
		for _, p := range lobby.drawingOrder {
			if p == player {
				inOrder = true
				break
			}
		}
		if inOrder {
			player.State = Guessing
			player.VoteTarget = ""
		} else {
			player.State = Spectator
			player.VoteTarget = ""
		}
	}

	// Get vote duration from settings, default to 15 seconds
	voteDuration := lobby.VoteDuration
	if voteDuration <= 0 {
		voteDuration = DefaultVoteDuration
	}

	// Set timer for voting phase
	lobby.RoundEndTime = time.Now().UTC().UnixNano()/1000000 + int64(voteDuration)*1000
	lobby.timeLeftTicker = time.NewTicker(1 * time.Second)
	go startTurnTimeTicker(lobby)

	// Notify all players to start voting
	lobby.TriggerUpdateEvent("voting-start", map[string]interface{}{
		"players":       lobby.players,
		"votingPlayers": lobby.drawingOrder, // only these are eligible targets/voters
		"round":         lobby.Round,
		"roundEndTime":  int(lobby.RoundEndTime - getTimeAsMillis()),
	})

	recalculateRanks(lobby)
}

// GameOverEvent is basically the ready event, but contains the last word.
// This is required in order to show the last player the word, in case they
// didn't manage to guess it in time. This is necessary since the last word
// is usually part of the "next-turn" event, which we don't send, since the
// game is over already.
type GameOverEvent struct {
	*Ready
	PreviousWord string `json:"previousWord"`
}

func endGame(lobby *Lobby) {
	lobby.drawer = nil
	lobby.Round = 0
	lobby.State = GameOver

	recalculateRanks(lobby)

	for _, player := range lobby.players {
		lobby.WriteJSON(player, GameEvent{
			Type: "game-over",
			Data: &GameOverEvent{
				PreviousWord: lobby.CurrentWord,
				Ready:        generateReadyData(lobby, player),
			}})
	}
}

// selectNextDrawer returns the next person that's supposed to be drawing, but
// doesn't tell the lobby yet. The boolean signals whether the current round
// is over.
func selectNextDrawer(lobby *Lobby) (*Player, bool) {
	for index, otherPlayer := range lobby.players {
		if otherPlayer == lobby.drawer {
			//If we have someone that's drawing, take the next one
			for i := index + 1; i < len(lobby.players); i++ {
				player := lobby.players[i]
				if player.Connected {
					return player, false
				}
			}

			//No player below the current drawer has been found, therefore we
			//fallback to our default logic at the bottom.
			break
		}
	}

	return lobby.players[0], true
}

// startTurnTimeTicker executes a loop that listens to the lobbies
// timeLeftTicker and executes a tickLogic on each tick. This method
// blocks until the turn ends.
func startTurnTimeTicker(lobby *Lobby) {
	for {
		ticker := lobby.timeLeftTicker
		if ticker == nil {
			return
		}
		<-ticker.C

		if !lobby.tickLogic() {
			break
		}
	}
}

// tickLogic checks whether the lobby needs to proceed to the next turn.
// The return value indicates whether additional ticks are necessary or not.
func (lobby *Lobby) tickLogic() bool {
	lobby.mutex.Lock()
	defer lobby.mutex.Unlock()

	currentTime := getTimeAsMillis()
	if currentTime >= lobby.RoundEndTime {
		if lobby.State == Voting {
			// Voting time expired, calculate scores with current votes
			calculateVotingScores(lobby)
		}
		advanceLobby(lobby)
		//Kill outer goroutine
		return false
	}

	return true
}

func getTimeAsMillis() int64 {
	return time.Now().UTC().UnixNano() / 1000000
}

// NextTurn represents the data necessary for displaying the lobby state right
// after a new turn started. Meaning that no word has been chosen yet and
// therefore there are no wordhints and no current drawing instructions.
type NextTurn struct {
	Round        int       `json:"round"`
	Players      []*Player `json:"players"`
	RoundEndTime int       `json:"roundEndTime"`
	PreviousWord *string   `json:"previousWord"`
}

// recalculateRanks will assign each player his respective rank in the lobby
// according to everyones current score. This will not trigger any events.
func recalculateRanks(lobby *Lobby) {
	sortedPlayers := make([]*Player, len(lobby.players))
	copy(sortedPlayers, lobby.players)
	sort.Slice(sortedPlayers, func(a, b int) bool {
		return sortedPlayers[a].Score > sortedPlayers[b].Score
	})

	//We start at maxint32, since we want the first player to cause an
	//increment of the the score, which will always happen this way, as
	//no player can have a score this high.
	lastScore := math.MaxInt32
	var lastRank int
	for _, player := range sortedPlayers {
		if !player.Connected {
			continue
		}

		if player.Score < lastScore {
			lastRank++
			player.Rank = lastRank
		} else {
			//Since the players are already sorted from high to low, we only
			//have the cases equal or higher.
			player.Rank = lastRank
		}

		lastScore = player.Score
	}
}

func createWordHintFor(word string, showAll bool) []*WordHint {
	wordHints := make([]*WordHint, 0, len(word))
	for _, char := range word {
		irrelevantChar := char == ' ' || char == '_' || char == '-'
		if showAll {
			wordHints = append(wordHints, &WordHint{
				Character: char,
				Underline: !irrelevantChar,
			})
		} else {
			if irrelevantChar {
				wordHints = append(wordHints, &WordHint{
					Character: char,
					Underline: !irrelevantChar,
				})
			} else {
				wordHints = append(wordHints, &WordHint{
					Underline: !irrelevantChar,
				})
			}
		}
	}

	return wordHints
}

func (lobby *Lobby) sendDataToEveryoneExceptSender(sender *Player, data interface{}) {
	for _, otherPlayer := range lobby.GetPlayers() {
		if otherPlayer != sender {
			lobby.WriteJSON(otherPlayer, data)
		}
	}
}

func (lobby *Lobby) TriggerUpdateEvent(eventType string, data interface{}) {
	event := &GameEvent{Type: eventType, Data: data}
	for _, otherPlayer := range lobby.GetPlayers() {
		lobby.WriteJSON(otherPlayer, event)
	}
}

func (lobby *Lobby) triggerUpdatePerPlayerEvent(eventType string, data func(*Player) interface{}) {
	for _, otherPlayer := range lobby.GetPlayers() {
		lobby.WriteJSON(otherPlayer, &GameEvent{Type: eventType, Data: data(otherPlayer)})
	}
}

func (lobby *Lobby) triggerPlayersUpdate() {
	lobby.TriggerUpdateEvent("update-players", lobby.players)
}

func (lobby *Lobby) triggerWordHintUpdate() {
	if lobby.CurrentWord == "" {
		return
	}

	lobby.triggerUpdatePerPlayerEvent("update-wordhint", func(player *Player) interface{} {
		return lobby.GetAvailableWordHints(player)
	})
}

// CreateLobby creates a new lobby including the initial player (owner) and
// optionally returns an error, if any occurred during creation.
func CreateLobby(playerName, chosenLanguage string, publicLobby bool, drawingTime, rounds, maxPlayers, customWordsChance, clientsPerIPLimit int, customWords []string, enableVotekick bool, wordsPerRound, numberOfSpies, voteDuration int) (*Player, *Lobby, error) {
	lobby := &Lobby{
		LobbyID: uuid.Must(uuid.NewV4()).String(),
		EditableLobbySettings: &EditableLobbySettings{
			Rounds:            rounds,
			DrawingTime:       drawingTime,
			MaxPlayers:        maxPlayers,
			CustomWordsChance: customWordsChance,
			ClientsPerIPLimit: clientsPerIPLimit,
			EnableVotekick:    enableVotekick,
			Public:            publicLobby,
			WordsPerRound:     wordsPerRound,
			NumberOfSpies:     numberOfSpies, // 0 means auto-calculate
			VoteDuration:      voteDuration,
		},
		CustomWords:    customWords,
		currentDrawing: make([]interface{}, 0),
		State:          Unstarted,
		mutex:          &sync.Mutex{},
		votes:          make(map[string]string),
		availableColors: initializeColors(),
	}

	if len(customWords) > 1 {
		rand.Shuffle(len(lobby.CustomWords), func(i, j int) {
			lobby.CustomWords[i], lobby.CustomWords[j] = lobby.CustomWords[j], lobby.CustomWords[i]
		})
	}

	lobby.Wordpack = chosenLanguage

	//Neccessary to correctly treat words from player, however, custom words might be treated incorrectly.
	lobby.lowercaser = cases.Lower(language.Make(getLanguageIdentifier(chosenLanguage)))

	//customWords are lowercased afterwards, as they are direct user input.
	if len(customWords) > 0 {
		for customWordIndex, customWord := range customWords {
			customWords[customWordIndex] = lobby.lowercaser.String(customWord)
		}
	}

	player := createPlayer(playerName)

	lobby.players = append(lobby.players, player)
	lobby.Owner = player
	lobby.creator = player

	words, err := readWordList(lobby.lowercaser, chosenLanguage)
	if err != nil {
		return nil, nil, err
	}

	lobby.words = words

	return player, lobby, nil
}

// generatePlayerName creates a new playername. A so called petname. It consists
// of an adverb, an adjective and a animal name. The result can generally be
// trusted to be sane.
func generatePlayerName() string {
	name := NameGenerator.PersianName()
	return name
}

// Message represents a message in the chatroom.
type Message struct {
	// Author is the player / thing that wrote the message
	Author string `json:"author"`
	// AuthorID is the unique identifier of the authors player object.
	AuthorID string `json:"authorId"`
	// Content is the actual message text.
	Content string `json:"content"`
}

// Ready represents the initial state that a user needs upon connection.
// This includes all the necessary things for properly running a client
// without receiving any more data.
type Ready struct {
	PlayerID     string `json:"playerId"`
	PlayerName   string `json:"playerName"`
	AllowDrawing bool   `json:"allowDrawing"`

	VotekickEnabled bool          `json:"votekickEnabled"`
	GameState       gameState     `json:"gameState"`
	OwnerID         string        `json:"ownerId"`
	Round           int           `json:"round"`
	Rounds          int           `json:"rounds"`
	RoundEndTime    int           `json:"roundEndTime"`
	WordHints       []*WordHint   `json:"wordHints"`
	Players         []*Player     `json:"players"`
	CurrentDrawing  []interface{} `json:"currentDrawing"`
	JoinedMidRound  bool          `json:"joinedMidRound"` // True if player joined during an ongoing round
}

func generateReadyData(lobby *Lobby, player *Player) *Ready {
	// Check if player joined mid-round (round is ongoing but player is not in drawing order)
	joinedMidRound := false
	if lobby.State == Ongoing && lobby.Round > 0 {
		// Check if player is in the drawing order
		inDrawingOrder := false
		for _, p := range lobby.drawingOrder {
			if p == player {
				inDrawingOrder = true
				break
			}
		}
		// If round is ongoing but player is not in drawing order, they joined mid-round
		joinedMidRound = !inDrawingOrder
	}
	
	ready := &Ready{
		PlayerID:     player.ID,
		AllowDrawing: player.State == Drawing && !joinedMidRound, // Don't allow drawing if joined mid-round
		PlayerName:   player.Name,

		VotekickEnabled: lobby.EnableVotekick,
		GameState:       lobby.State,
		OwnerID:         lobby.Owner.ID,
		Round:           lobby.Round,
		Rounds:          lobby.Rounds,
		WordHints:       lobby.GetAvailableWordHints(player),
		Players:         lobby.players,
		CurrentDrawing:  lobby.currentDrawing,
		JoinedMidRound:  joinedMidRound,
	}

	if lobby.State != Ongoing {
		//Clients should interpret 0 as "time over", unless the gamestate isn't "ongoing"
		ready.RoundEndTime = 0
	} else {
		ready.RoundEndTime = int(lobby.RoundEndTime - getTimeAsMillis())
		// SpyDrawer: Send current word to mid-round joiners so they can see it
		// The word will also be sent in the next drawing-turn event, but send it here too
		// for immediate display
		if joinedMidRound && lobby.CurrentWord != "" && lobby.drawer != nil {
			// Send a drawing-turn-like event immediately so they see the word
			wordLength := len([]rune(lobby.CurrentWord))
			lobby.WriteJSON(player, GameEvent{
				Type: "drawing-turn",
				Data: map[string]interface{}{
					"drawer":       lobby.drawer.ID,
					"roundEndTime": int(lobby.RoundEndTime - getTimeAsMillis()),
					"players":      lobby.players,
					"currentWord":  lobby.CurrentWord,
					"wordLength":   wordLength,
				},
			})
		}
	}

	return ready
}

func (lobby *Lobby) OnPlayerConnectUnsynchronized(player *Player) {
	player.Connected = true
	
	// Assign color if player doesn't have one
	if len(lobby.availableColors) > 0 && (player.Color.R == 0 && player.Color.G == 0 && player.Color.B == 0) {
		// Find an unused color
		usedColors := make(map[RGBColor]bool)
		for _, p := range lobby.players {
			if p != player && p.Connected {
				usedColors[p.Color] = true
			}
		}
		for _, color := range lobby.availableColors {
			if !usedColors[color] {
				player.Color = color
				break
			}
		}
	}
	
	recalculateRanks(lobby)
	lobby.WriteJSON(player, GameEvent{Type: "ready", Data: generateReadyData(lobby, player)})

	// SpyDrawer: If a player connects mid-round, mark them as spectator until next round.
	if lobby.Round > 0 && (lobby.State == Ongoing || lobby.State == Voting) {
		inOrder := false
		for _, p := range lobby.drawingOrder {
			if p == player {
				inOrder = true
				break
			}
		}
		if !inOrder {
			player.State = Spectator
		}
	}

	//TODO Only send to everyone except for the new player, since it's part of the ready event.
	lobby.triggerPlayersUpdate()
}

func (lobby *Lobby) OnPlayerDisconnect(player *Player) {
	//We want to avoid calling the handler twice.
	if player.ws == nil {
		return
	}
	disconnectTime := time.Now()

	//It is important to properly disconnect the player before aqcuiring the mutex
	//in order to avoid false assumptions about the players connection state
	//and avoid attempting to send events.
	log.Printf("Player %s(%s) disconnected.\n", player.Name, player.ID)
	player.Connected = false
	player.ws = nil

	lobby.mutex.Lock()
	defer lobby.mutex.Unlock()

	player.disconnectTime = &disconnectTime
	lobby.LastPlayerDisconnectTime = &disconnectTime

	// SpyDrawer: If a spy disconnects during an ongoing round, cancel the round
	if lobby.State == Ongoing && player.IsSpy {
		log.Printf("SpyDrawer: Spy %s disconnected during round %d, canceling round\n", player.Name, lobby.Round)
		// Cancel current round and start a new one
		lobby.State = Unstarted
		lobby.drawer = nil
		lobby.currentDrawing = make([]interface{}, 0)
		lobby.currentPlayerIndex = 0
		lobby.currentTurnNumber = 0
		lobby.RoundEndTime = 0
		if lobby.timeLeftTicker != nil {
			lobby.timeLeftTicker.Stop()
		}
		
		// Notify all players that the round was canceled
		lobby.TriggerUpdateEvent("round-canceled", map[string]interface{}{
			"reason": "جاسوس از بازی خارج شد",
			"players": lobby.players,
		})
		
		// Start a new round
		if lobby.hasConnectedPlayersInternal() && lobby.GetConnectedPlayerCount() >= 2 {
			startNewRound(lobby)
		}
	} else if lobby.drawer == player {
		// If drawer (non-spy) disconnects, advance to next turn
		advanceLobby(lobby)
	}

	recalculateRanks(lobby)
	if lobby.hasConnectedPlayersInternal() {
		lobby.triggerPlayersUpdate()
	}
}

// GetAvailableWordHints returns a WordHint array depending on the players
// game state, since people that are drawing or have already guessed correctly
// can see all hints.
func (lobby *Lobby) GetAvailableWordHints(player *Player) []*WordHint {
	// SpyDrawer: spies only see blanks (letter count); others see full word.
	if player.IsSpy {
		return lobby.wordHints
	}
	return lobby.wordHintsShown
}

// JoinPlayer creates a new player object using the given name and adds it
// to the lobbies playerlist. The new players is returned.
func (lobby *Lobby) JoinPlayer(playerName string) *Player {
	player := createPlayer(playerName)

	lobby.players = append(lobby.players, player)

	// Assign a color to the new player if colors are initialized
	if len(lobby.availableColors) > 0 {
		// Find an unused color
		usedColors := make(map[RGBColor]bool)
		for _, p := range lobby.players {
			if p.Connected && p != player {
				usedColors[p.Color] = true
			}
		}
		for _, color := range lobby.availableColors {
			if !usedColors[color] {
				player.Color = color
				break
			}
		}
	}

	return player
}

func (lobby *Lobby) canDraw(player *Player) bool {
	// In SpyDrawer, check if it's this player's turn
	if len(lobby.drawingOrder) == 0 {
		return false
	}
	if lobby.currentPlayerIndex >= len(lobby.drawingOrder) {
		return false
	}
	currentDrawer := lobby.drawingOrder[lobby.currentPlayerIndex]
	return currentDrawer == player && lobby.State == Ongoing && lobby.CurrentWord != ""
}

// handleVoteEvent processes a vote during the voting phase
func handleVoteEvent(lobby *Lobby, voter *Player, votedForID string) {
	// SpyDrawer: Only round participants (drawingOrder) may vote, and only for other participants.
	inOrder := func(p *Player) bool {
		for _, pp := range lobby.drawingOrder {
			if pp == p {
				return true
			}
		}
		return false
	}
	inOrderID := func(id string) bool {
		for _, pp := range lobby.drawingOrder {
			if pp != nil && pp.ID == id {
				return true
			}
		}
		return false
	}
	if !inOrder(voter) {
		return
	}
	if !inOrderID(votedForID) {
		return
	}

	// Check if voter already voted
	if _, alreadyVoted := lobby.votes[voter.ID]; alreadyVoted {
		return
	}

	// Check if voted-for player exists
	var votedForPlayer *Player
	for _, p := range lobby.players {
		if p.ID == votedForID && p.Connected {
			votedForPlayer = p
			break
		}
	}

	if votedForPlayer == nil {
		return
	}

	// Record the vote
	lobby.votes[voter.ID] = votedForID
	voter.VoteTarget = votedForID

	// Send chat message about the vote
	voteMessage := fmt.Sprintf("%s رای داد به %s", voter.Name, votedForPlayer.Name)
	lobby.TriggerUpdateEvent("message", Message{
		Author:   "سیستم",
		AuthorID: "system",
		Content:  voteMessage,
	})

	// Check if everyone has voted
	connectedCount := 0
	for _, p := range lobby.players {
		if p.Connected {
			connectedCount++
		}
	}

	if len(lobby.votes) >= connectedCount {
		// All votes are in, calculate scores and advance
		calculateVotingScores(lobby)
		advanceLobby(lobby)
	} else {
		// Update players with current vote status
		lobby.triggerPlayersUpdate()
	}
}

// calculateVotingScores calculates scores based on voting results
func calculateVotingScores(lobby *Lobby) {
	// Count votes for each player
	voteCounts := make(map[string]int)
	for _, votedForID := range lobby.votes {
		voteCounts[votedForID]++
	}

	// Reset last scores
	for _, player := range lobby.players {
		player.LastScore = 0
	}

	// Calculate scores for spies
	for _, player := range lobby.players {
		if !player.Connected {
			continue
		}

		if player.IsSpy {
			// Spy gets 3 points if not recognized (0 or 1 votes against them)
			votesAgainst := voteCounts[player.ID]
			if votesAgainst <= 1 {
				player.LastScore = 3
				player.Score += 3
			}
		}
	}

	// Calculate scores for non-spies (1 point for each correct guess)
	for voterID, votedForID := range lobby.votes {
		// Find the voter
		var voter *Player
		for _, p := range lobby.players {
			if p.ID == voterID {
				voter = p
				break
			}
		}
		if voter == nil || !voter.Connected || voter.IsSpy {
			continue
		}

		// Find who they voted for
		var votedFor *Player
		for _, p := range lobby.players {
			if p.ID == votedForID {
				votedFor = p
				break
			}
		}
		if votedFor != nil && votedFor.IsSpy {
			// Correct guess! Non-spy gets 1 point
			voter.LastScore = 1
			voter.Score += 1
		}
	}
}

var connectionCharacterReplacer = strings.NewReplacer(" ", "", "-", "", "_", "")

// simplifyText prepares the string for a more lax comparison of two words.
// Spaces, dashes, underscores and accented characters are removed or replaced.
func simplifyText(s string) string {
	return connectionCharacterReplacer.
		Replace(sanitize.Accents(s))
}
