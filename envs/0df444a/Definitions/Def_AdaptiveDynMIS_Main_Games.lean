-- Prove2me | Definitions.Def_AdaptiveDynMIS_Main_Games
-- name    : AdaptiveDynMIS_Main_Games
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:54:56.5652+00:00
-- url     : https://prove2.me/theorems/a408fdc4-ec5a-4743-8539-c8dfd6f5bd80
-- title:
--   The membership-query game and the emptiness-query game on hidden Bernoulli(p) bits
-- statement:
--   Both games are played against hidden independent bits. The universe $U$ starts empty and always satisfies $|U|\le k$. Each newly inserted element $e$ receives a hidden bit $X_e\sim\mathrm{Bernoulli}(p)$, independent of everything else, and the **sampled subset** is
--   $$S=\{e\in U:\ X_e=1\}.$$
--   A later insertion, also one with a reused name, creates a new element with a fresh bit; elements are therefore identified by their insertion number, and the bits form an i.i.d. $\mathrm{Bernoulli}(p)$ sequence $X_0,X_1,\dots$ (`bitsMeasure p`). One step is one move.
--
--   **Membership-query game** (Lemma 3.2). A move is: insert a fresh element; reveal and delete an element $e\in U$ (the player learns $X_e$, and $e$ leaves $U$ and $S$); query an element $e\in U$ (the player learns $X_e$; repeated queries are allowed). A yes answer lets the game continue, the first no answer ends it.
--
--   **Emptiness-query game** (Lemma 3.5). A move is: insert a fresh element; delete an element $e\in U$ (nothing is revealed); ask whether $S$ is empty (the only information about the bits); or stop voluntarily. A nonempty answer lets the game continue, the first empty answer ends it.
--
--   In both games the player chooses each move from everything it has observed: its earlier moves and their answers. `memStateAt k X A j` and `empStateAt k X A j` are the states (the universe $U$, the number of insertions, the player's view, whether the game has ended) after $j$ steps of the deterministic player $A$ on the bits $X$.
--
--   These games model what an adaptive adversary learns about the algorithm's private samples through the reported MISs.
--
--   **Formalization Note.** A player is a deterministic function of its view (the list of its moves with their answers); a randomized player is a mixture of these. A move that is not available (an insertion when $|U|=k$, a deletion or query of an element outside $U$) ends the game, like a voluntary stop; in the membership game the player may stop in this way, since it "takes at most $M$ steps". After the game has ended the state stays fixed, so the states after steps $0,1,\dots,M$ are exactly the states reached by a player taking at most $M$ steps. The Bernoulli law is Mathlib's `bernoulliMeasure true false` with the parameter clamped to $[0,1]$.
-- source:
--   Chen, Fan, Zhang, Faster Dynamic Maximal Independent Set against Adaptive Adversaries, arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), pp. 20–23, §3 'Probabilistic games', Lemmas 3.2 and 3.5

import Mathlib

namespace AdaptiveDynMIS.Main

open MeasureTheory ProbabilityTheory

/-! # The membership-query game (Lemma 3.2) and the emptiness-query game (Lemma 3.5)

Chen, Fan, Zhang, *Faster Dynamic Maximal Independent Set against Adaptive Adversaries*,
arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), §3 "Probabilistic games", pp. 20–23 (PDF 22–25).

**Formalization Note.**
* Elements are identified by their insertion number: the `(i+1)`-st insertion of the game creates
  element `i` with the hidden bit `X i`. A later insertion, also one under a reused name, is a new
  element with a new index and so a fresh bit. The bits `X : ℕ → Bool` are i.i.d. `Bernoulli(p)`
  under `bitsMeasure p`.
* The player is a deterministic strategy: its next move is a function of its view, the list of its
  moves so far with the answer each one received (`none` for a move that reveals nothing). A
  randomized player is a mixture of deterministic ones.
* A move that is not available (an insertion when `|U| = k`, a deletion or query of an element not in
  `U`) ends the game, as does a voluntary stop and the terminating answer. After the end the state
  stays fixed.
* One step is one move. `memStateAt k X A j` (`empStateAt k X A j`) is the state after `j` steps,
  `j = 0, 1, …`; the states reached by a player that takes at most `M` steps are those with
  `j ≤ M`. -/

/-- `Bernoulli(p)` bits, clamped to `[0, 1]`: `true` with probability `p`. -/
noncomputable def bitLaw (p : ℝ) : Measure Bool :=
  bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one p)

/-- The law of the hidden bits: i.i.d. `Bernoulli(p)`, indexed by insertion number. -/
noncomputable def bitsMeasure (p : ℝ) : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => bitLaw p

/-- The sampled subset `S = {e ∈ U : X_e = 1}` of a set `U` of element indices. -/
def sampled (X : ℕ → Bool) (U : Finset ℕ) : Finset ℕ :=
  U.filter fun e => X e = true

/-! ## The membership-query game (Lemma 3.2) -/

/-- A move of the membership-query game: insert a fresh element, reveal and delete element `e`,
ask whether element `e` belongs to `S`, or stop. -/
inductive MemMove where
  | insert
  | revealDelete (e : ℕ)
  | query (e : ℕ)
  | stop
  deriving DecidableEq

/-- A deterministic player of the membership-query game: its next move as a function of its view
(each earlier move with its answer: the revealed bit of a reveal-and-delete, the answer of a query,
`none` for an insertion). -/
abbrev MemStrategy := List (MemMove × Option Bool) → MemMove

/-- A state of the membership-query game: the current universe `U` (element indices), the number of
insertions so far, the player's view, and whether the game has ended. -/
structure MemState where
  U : Finset ℕ
  next : ℕ
  view : List (MemMove × Option Bool)
  ended : Bool

/-- The initial state: `U = ∅`, nothing inserted, nothing seen. -/
def MemState.init : MemState := ⟨∅, 0, [], false⟩

/-- One step of the membership-query game with universe bound `k` and hidden bits `X`. An insertion
adds the next index to `U` (only while `|U| < k`); reveal-and-delete of `e ∈ U` reveals `X e` and
removes `e`; a query of `e ∈ U` reveals `X e` and ends the game when the answer is no. -/
def memStep (k : ℕ) (X : ℕ → Bool) (A : MemStrategy) (s : MemState) : MemState :=
  if s.ended then s else
  match A s.view with
  | .insert =>
      if s.U.card < k then
        ⟨insert s.next s.U, s.next + 1, s.view ++ [(.insert, none)], false⟩
      else { s with ended := true }
  | .revealDelete e =>
      if e ∈ s.U then
        ⟨s.U.erase e, s.next, s.view ++ [(.revealDelete e, some (X e))], false⟩
      else { s with ended := true }
  | .query e =>
      if e ∈ s.U then
        ⟨s.U, s.next, s.view ++ [(.query e, some (X e))], !(X e)⟩
      else { s with ended := true }
  | .stop => { s with ended := true }

/-- The state of the membership-query game after `j` steps. -/
def memStateAt (k : ℕ) (X : ℕ → Bool) (A : MemStrategy) : ℕ → MemState
  | 0 => MemState.init
  | j + 1 => memStep k X A (memStateAt k X A j)

/-! ## The emptiness-query game (Lemma 3.5) -/

/-- A move of the emptiness-query game: insert a fresh element, delete element `e` (revealing
nothing), ask whether `S` is empty, or stop. -/
inductive EmpMove where
  | insert
  | delete (e : ℕ)
  | query
  | stop
  deriving DecidableEq

/-- A deterministic player of the emptiness-query game: its next move as a function of its view
(each earlier move with its answer: `some true` for "nonempty", `some false` for "empty", `none` for
an insertion or deletion). -/
abbrev EmpStrategy := List (EmpMove × Option Bool) → EmpMove

/-- A state of the emptiness-query game: the current universe `U` (element indices), the number of
insertions so far, the player's view, and whether the game has ended. -/
structure EmpState where
  U : Finset ℕ
  next : ℕ
  view : List (EmpMove × Option Bool)
  ended : Bool

/-- The initial state: `U = ∅`, nothing inserted, nothing seen. -/
def EmpState.init : EmpState := ⟨∅, 0, [], false⟩

/-- One step of the emptiness-query game with universe bound `k` and hidden bits `X`. An insertion
adds the next index to `U` (only while `|U| < k`); deletion of `e ∈ U` removes it and reveals
nothing; a query reveals only whether `S` is nonempty and ends the game when `S` is empty. -/
def empStep (k : ℕ) (X : ℕ → Bool) (A : EmpStrategy) (s : EmpState) : EmpState :=
  if s.ended then s else
  match A s.view with
  | .insert =>
      if s.U.card < k then
        ⟨insert s.next s.U, s.next + 1, s.view ++ [(.insert, none)], false⟩
      else { s with ended := true }
  | .delete e =>
      if e ∈ s.U then
        ⟨s.U.erase e, s.next, s.view ++ [(.delete e, none)], false⟩
      else { s with ended := true }
  | .query =>
      ⟨s.U, s.next, s.view ++ [(.query, some (decide (sampled X s.U).Nonempty))],
        !(decide (sampled X s.U).Nonempty)⟩
  | .stop => { s with ended := true }

/-- The state of the emptiness-query game after `j` steps. -/
def empStateAt (k : ℕ) (X : ℕ → Bool) (A : EmpStrategy) : ℕ → EmpState
  | 0 => EmpState.init
  | j + 1 => empStep k X A (empStateAt k X A j)

end AdaptiveDynMIS.Main


