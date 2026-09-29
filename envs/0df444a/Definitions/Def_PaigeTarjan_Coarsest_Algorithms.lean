-- Prove2me | Definitions.Def_PaigeTarjan_Coarsest_Algorithms
-- name    : PaigeTarjan_Coarsest_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:46:08.342333+00:00
-- url     : https://prove2.me/theorems/d53694d1-64af-4817-9705-795ab91c1e5e
-- title:
--   The naïve and the improved (smaller-half) refinement algorithms as step relations and runs
-- statement:
--   This file encodes the two refinement algorithms for the relational coarsest partition problem as step relations, and their executions as finite runs. Throughout, $E$ is a relation on a finite set $U$, $P$ is the initial partition, and $\mathrm{split}(S,Q)$ is the refinement of $Q$ by the preimage $E^{-1}(S)$.
--
--   1. **Naïve step.** From a partition $Q$, choose a set $S$ that is a union of some of the blocks of $Q$ and is a **splitter** of $Q$, i.e. $\mathrm{split}(S,Q) \neq Q$; the new partition is $\mathrm{split}(S,Q)$. A naïve run of $K$ steps is a sequence $Q_0 = P, Q_1, \dots, Q_K$ in which each $Q_{j+1}$ arises from $Q_j$ by a naïve step.
--   2. **Improved step.** The state is a pair $(Q, X)$ of partitions. Choose a block $S \in X$ that is not a block of $Q$ and a block $B \in Q$ with $B \subseteq S$ and $|B| \le |S|/2$. Replace $S$ within $X$ by the two sets $B$ and $S - B$, and replace $Q$ by
--   $$\mathrm{split}\bigl(S - B,\ \mathrm{split}(B, Q)\bigr).$$
--   An improved run of $K$ steps is a sequence of states $(Q_0, X_0) = (P, \{U\}), \dots, (Q_K, X_K)$ together with the sets $S_j, B_j$ chosen in step $j$ ($0 \le j < K$).
--
--   The naïve algorithm repeats its step until $Q$ is stable; the improved algorithm repeats its step until $Q = X$. Recording the chosen $B_j$ in a run is what allows statements counting how often an element lies in a refining block.
--
--   **Formalization Note** Runs are indexed by `Fin (K + 1)` (states) and `Fin K` (steps). The size condition $|B| \le |S|/2$ is written `2 * B.card ≤ S.card` to avoid natural-number division. The step relations say only which moves are allowed; they do not fix a choice rule, so every statement about runs holds for every sequence of choices.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 978 (naïve algorithm, step Refine) and p. 979 (improved algorithm, step Refine)

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

namespace PaigeTarjan.Coarsest

/-!
The two refinement algorithms of §3 (Paige–Tarjan 1987, pp. 978–979) as step relations and
finite runs.
-/

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- One step of the naïve algorithm (p. 978): find a set `S` that is a union of some of the
blocks of `Q` and is a splitter of `Q` (`split(S, Q) ≠ Q`); replace `Q` by `split(S, Q)`. -/
def NaiveStep (E : U → U → Prop) [DecidableRel E] (Q Q' : Finset (Finset U)) : Prop :=
  ∃ S : Finset U, IsUnionOfBlocks S Q ∧ split E S Q ≠ Q ∧ Q' = split E S Q

/-- A run of `K` naïve refinement steps from the initial partition `P`: states
`Qs 0 = P, Qs 1, …, Qs K`, consecutive states related by `NaiveStep`. -/
def IsNaiveRun (E : U → U → Prop) [DecidableRel E] (P : Finset (Finset U)) (K : ℕ)
    (Qs : Fin (K + 1) → Finset (Finset U)) : Prop :=
  Qs 0 = P ∧ ∀ j : Fin K, NaiveStep E (Qs j.castSucc) (Qs j.succ)

/-- One step of the improved algorithm (p. 979), from the pair `(Q, X)` to `(Q', X')`, recording
the chosen sets `S` and `B`: `S` is a block of `X` that is not a block of `Q`; `B` is a block of
`Q` with `B ⊆ S` and `|B| ≤ |S|/2` (written `2|B| ≤ |S|`); `S` is replaced within `X` by the two
sets `B` and `S − B`; `Q` is replaced by `split(S − B, split(B, Q))`. -/
def ImprovedStep (E : U → U → Prop) [DecidableRel E] (Q X : Finset (Finset U))
    (S B : Finset U) (Q' X' : Finset (Finset U)) : Prop :=
  S ∈ X ∧ S ∉ Q ∧ B ∈ Q ∧ B ⊆ S ∧ 2 * B.card ≤ S.card ∧
    X' = insert B (insert (S \ B) (X.erase S)) ∧
    Q' = split E (S \ B) (split E B Q)

/-- A run of `K` steps of the improved algorithm from the initial partition `P`: states
`(Qs j, Xs j)` for `j = 0, …, K` with `Qs 0 = P` and `Xs 0 = {U}`, and the sets `Ss j`, `Bs j`
chosen in step `j` (`j = 0, …, K − 1`). -/
def IsImprovedRun (E : U → U → Prop) [DecidableRel E] (P : Finset (Finset U)) (K : ℕ)
    (Qs Xs : Fin (K + 1) → Finset (Finset U)) (Ss Bs : Fin K → Finset U) : Prop :=
  Qs 0 = P ∧ Xs 0 = {Finset.univ} ∧
    ∀ j : Fin K, ImprovedStep E (Qs j.castSucc) (Xs j.castSucc) (Ss j) (Bs j)
      (Qs j.succ) (Xs j.succ)

end PaigeTarjan.Coarsest


