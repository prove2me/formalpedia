-- Prove2me | Definitions.Def_LocalBreadth_GameRun
-- name    : LocalBreadth_GameRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:22.139195+00:00
-- url     : https://prove2.me/theorems/50905c72-ad9a-4ec0-9ef7-271b640a806c
-- title:
--   The local pairing game
-- statement:
--   A finite board $B$ is revealed through an increasing filtration $\emptyset=Y_0\subseteq Y_1\subseteq\dots\subseteq Y_m=B$. On each turn the adversary selects a visible point, with repetitions allowed, and the algorithm selects an unused visible point if one remains. Other events may also select unused points of $B$ for the algorithm, whether or not visible.
--
--   Points selected by the algorithm are **white**, and they remain white after later inputs; other points selected by the adversary are **black**; the rest are **unused**. A legal log is a list of reveal events, turns and external selections following these rules from the empty position.
--
--   **Formalization Note** A turn is the pair of the adversary's point and the algorithm's response; the response is `none` only when no visible point is unused after the adversary's selection.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Lemma 5.18, p.36

import Mathlib

namespace LocalBreadth

/-- One event of the **local pairing game**. Kleinberg, Wei, STOC 2027 submission (manuscript sha256
f924cbfc…), Lemma 5.18, p.36. -/
inductive GameEvent where
  /-- Visibility moves to the next level of the filtration. -/
  | reveal : GameEvent
  /-- A turn: the adversary selects `y`, and the algorithm responds with `r` (`none` if no unused
  visible point remains). -/
  | turn (y : ℤ) (r : Option ℤ) : GameEvent
  /-- Another event selects the unused point `y` for the algorithm, whether or not it is visible. -/
  | external (y : ℤ) : GameEvent

/-- The position of the game: the visibility level, the black points (selected by the adversary and not
by the algorithm before), and the white points (selected by the algorithm). -/
structure GameState where
  /-- The index `i` of the visible set `Y i`. -/
  level : ℕ
  /-- Adversary-selected points that were not white. -/
  black : Finset ℤ
  /-- Algorithm-selected points. -/
  white : Finset ℤ

/-- The points of the board neither black nor white (p.36: "the rest unused"). -/
def GameState.unused (B : Finset ℤ) (s : GameState) : Finset ℤ := B \ (s.black ∪ s.white)

/-- The adversary selects `y`: white points remain white after later inputs, and any other point is
black from now on. -/
def GameState.mark (y : ℤ) (s : GameState) : GameState :=
  if y ∈ s.white then s else ⟨s.level, insert y s.black, s.white⟩

/-- The algorithm selects `z`. -/
def GameState.paint (z : ℤ) (s : GameState) : GameState := ⟨s.level, s.black, insert z s.white⟩

/-- The legal moves, Lemma 5.18. A turn: the adversary selects a visible point, with repetitions allowed,
and the algorithm selects an unused visible point if one remains. An external event selects an unused
point of `B`, visible or not. -/
inductive GameStep (B : Finset ℤ) (Y : ℕ → Finset ℤ) (m : ℕ) : GameState → GameEvent → GameState → Prop
  | reveal (s : GameState) (h : s.level < m) :
      GameStep B Y m s .reveal ⟨s.level + 1, s.black, s.white⟩
  | turn_some (s : GameState) (y z : ℤ) (hy : y ∈ Y s.level) (hz : z ∈ Y s.level)
      (hu : z ∈ (s.mark y).unused B) :
      GameStep B Y m s (.turn y (some z)) ((s.mark y).paint z)
  | turn_none (s : GameState) (y : ℤ) (hy : y ∈ Y s.level)
      (hu : ∀ z ∈ Y s.level, z ∉ (s.mark y).unused B) :
      GameStep B Y m s (.turn y none) (s.mark y)
  | external (s : GameState) (z : ℤ) (hu : z ∈ s.unused B) :
      GameStep B Y m s (.external z) (s.paint z)

/-- A legal log, oldest event first, from the start (`Y 0` visible, nothing selected) to the state `s`. -/
inductive GameRun (B : Finset ℤ) (Y : ℕ → Finset ℤ) (m : ℕ) : List GameEvent → GameState → Prop
  | nil : GameRun B Y m [] ⟨0, ∅, ∅⟩
  | snoc {log : List GameEvent} {s s' : GameState} {e : GameEvent} (h : GameRun B Y m log s)
      (hs : GameStep B Y m s e s') : GameRun B Y m (log ++ [e]) s'

end LocalBreadth


