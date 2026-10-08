-- Prove2me | Definitions.Def_ObliviousRAM_LowerBound_Game
-- name    : ObliviousRAM_LowerBound_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:30.471007+00:00
-- url     : https://prove2.me/theorems/1fbd0563-507c-497d-a43a-bccdcf5dfb77
-- title:
--   §6, pp. 469–470 — ball-and-cell game and oblivious randomized player
-- statement:
--   The **ball-and-cell game** has $m$ balls and $m$ cells, each of which holds at most one ball. Initially ball $i$ occupies cell $i$ and the player's hand is empty. A player may hold at most $b$ balls. At each access the player names a cell and either removes its ball into a nonfull hand, places a ball from the hand into an empty cell, or does nothing. The observer sees the cell, but not which of these actions occurred.
--
--   A run $a$ **satisfies** a request sequence $r_1,\ldots,r_t$ when it is legal and there are nondecreasing access indices $1\le j_1\le\cdots\le j_t=|a|$ such that the player holds ball $r_i$ after access $j_i$ for every round $i$. The player may know all requests before acting. Its response to each sequence is a probability distribution on finite runs. It is **correct** when every run with positive probability satisfies its requests, and **oblivious** when the probability distribution of the visible cell sequence is identical for every pair of request sequences.
--
--   This model isolates the access-pattern lower bound in the proof of Theorem 6.1 and permits reusing its state transition and observer definitions in related counting arguments.
--
--   **Formalization Note** The paper's labels $[m]=\{1,\ldots,m\}$ and rounds $1,\ldots,t$ are represented by zero-based `Fin m` and `Fin t`; action counts remain one-based. Illegal moves return `none`, and the hand after an illegal prefix is used only under legality. The case $t=0$ has no round-end constraints.
-- source:
--   Goldreich and Ostrovsky, Software protection and simulation on oblivious RAMs, J. ACM 43 (1996), pp. 469–470, §6, proof of THEOREM 6.1; https://doi.org/10.1145/233551.233553

import Mathlib

namespace ObliviousRAM.LowerBound

/-- The unobserved operation during one access. -/
inductive Hidden (m : ℕ) where
  | take
  | place (ball : Fin m)
  | nothing
  deriving DecidableEq, Fintype

/-- An accessed cell and the operation performed there. -/
abbrev Action (m : ℕ) := Fin m × Hidden m

/-- The contents of every cell and the balls held by the player. -/
structure State (m : ℕ) where
  cell : Fin m → Option (Fin m)
  hand : Finset (Fin m)

/-- Ball `i` begins in cell `i`, and the hand begins empty. -/
def initState (m : ℕ) : State m := ⟨fun i => some i, ∅⟩

/-- One legal access; `none` marks an illegal attempted move. -/
def step {m : ℕ} (b : ℕ) (s : State m) (a : Action m) : Option (State m) :=
  match a with
  | (v, .take) =>
      match s.cell v with
      | none => none
      | some β =>
          if s.hand.card < b then
            some ⟨Function.update s.cell v none, insert β s.hand⟩
          else none
  | (v, .place β) =>
      if s.cell v = none ∧ β ∈ s.hand then
        some ⟨Function.update s.cell v (some β), s.hand.erase β⟩
      else none
  | (_, .nothing) => some s

/-- The state after the first `j` accesses, if all were legal. -/
def stateAfter {m : ℕ} (b : ℕ) (a : List (Action m)) (j : ℕ) : Option (State m) :=
  (a.take j).foldl (fun os act => os.bind (fun s => step b s act)) (some (initState m))

/-- Every operation in a run is legal. -/
def Legal {m : ℕ} (b : ℕ) (a : List (Action m)) : Prop :=
  (stateAfter b a a.length).isSome

/-- The balls held after `j` accesses; this is used only for legal runs. -/
def handAfter {m : ℕ} (b : ℕ) (a : List (Action m)) (j : ℕ) : Finset (Fin m) :=
  ((stateAfter b a j).map State.hand).getD ∅

/-- A legal run completes the requested rounds at monotone, possibly repeated access indices. -/
def Satisfies {m t : ℕ} (b : ℕ) (a : List (Action m)) (r : Fin t → Fin m) : Prop :=
  Legal b a ∧
    ∃ j : Fin t → ℕ,
      Monotone j ∧
      (∀ i, 1 ≤ j i) ∧
      (∀ i, j i ≤ a.length) ∧
      (∀ i : Fin t, (i : ℕ) + 1 = t → j i = a.length) ∧
      ∀ i, r i ∈ handAfter b a (j i)

/-- The sequence of cells seen by the observer. -/
def visible {m : ℕ} (a : List (Action m)) : List (Fin m) := a.map Prod.fst

/-- A randomized player that handles every request and has a request-independent visible law. -/
structure ObliviousPlayer (b m t : ℕ) where
  play : (Fin t → Fin m) → PMF (List (Action m))
  correct : ∀ r, ∀ a ∈ (play r).support, Satisfies b a r
  oblivious : ∀ r r', (play r).map visible = (play r').map visible

end ObliviousRAM.LowerBound


