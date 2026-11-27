-- Prove2me | Definitions.Def_RandomGreedyMIS_basic
-- name    : RandomGreedyMIS_basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T04:28:26.258214+00:00
-- url     : https://prove2.me/theorems/46d3fa3c-aa95-5b47-adff-7ffce9f00eb2
-- title:
--   Recursive randomized greedy MIS oracle and its number of calls
-- statement:
--   The recursive randomized greedy maximal independent set oracle (Nguyen–Onak; Yoshida–Yamamoto–Ito). Let $G$ be a finite simple graph on $\{0,\dots,n-1\}$ and $\pi$ a permutation of the vertices, read as a ranking (vertex $v$ has rank $\pi(v)$).
--
--   1. `inMIS G π v`: $v$ belongs to the greedy maximal independent set for the ranking $\pi$, i.e. (by recursion on the rank) no neighbour $w$ of $v$ with $\pi(w)<\pi(v)$ belongs to it.
--   2. `lowerNbrs G π v`: the neighbours $w$ of $v$ with $\pi(w)<\pi(v)$, listed in increasing order of rank.
--   3. `calls G π v`: the number of recursive calls made by the oracle $\mathrm{RGMIS}(v,\pi)$, which examines the lower-ranked neighbours $w_1,w_2,\dots$ in increasing rank, calls $\mathrm{RGMIS}(w_i,\pi)$ for each, and stops right after the first $w_i$ that is in the independent set. Each call to $w_i$ costs $1+\mathrm{calls}(w_i)$; there is no memoisation, and the top-level invocation is not counted.
--
--   Applied to the line graph, the same oracle decides membership of an edge in the random greedy maximal matching; this is the local oracle behind sublinear matching-size estimators.
--
--   **Formalization Note** `inMIS` and `calls` are defined by well-founded recursion on the rank; `loopCost` evaluates the early-stopping loop.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, A Simple Average-case Analysis of Recursive Randomized Greedy MIS, arXiv:2604.01462 (2026), Algorithm 2; Yoshida, Yamamoto, Ito, STOC 2009; Nguyen, Onak, FOCS 2008.

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace RandomGreedyMIS

open Finset

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

set_option linter.unusedVariables false in
/-- Greedy MIS membership: `v` is in the greedy MIS (w.r.t. rank `π`) iff no neighbour of
smaller rank is in it. Well-founded recursion on `π v`. -/
def inMIS (π : Equiv.Perm (Fin n)) (v : Fin n) : Bool :=
  (List.finRange n).all fun w =>
    if h : G.Adj v w ∧ π w < π v then !(inMIS π w) else true
termination_by (π v : ℕ)
decreasing_by exact h.2

/-- The neighbours of `v` of smaller rank, listed in increasing order of rank. -/
def lowerNbrs (π : Equiv.Perm (Fin n)) (v : Fin n) : List (Fin n) :=
  ((List.finRange n).map π.symm).filter fun w => decide (G.Adj v w ∧ π w < π v)

lemma mem_lowerNbrs (π : Equiv.Perm (Fin n)) (v w : Fin n) :
    w ∈ lowerNbrs G π v ↔ G.Adj v w ∧ π w < π v := by
  simp [lowerNbrs, List.mem_filter, List.mem_map]
  intro _ _
  exact ⟨π w, by simp⟩

/-- The oracle loop: given, in order, the pairs `(inMIS w_i, cost of the call to w_i)`, it pays
for calls until (and including) the first `w_i` that is in the MIS. -/
def loopCost : List (Bool × ℕ) → ℕ
  | [] => 0
  | (b, c) :: rest => c + (if b then 0 else loopCost rest)

/-- Number of recursive calls made by the top-level invocation `RGMIS(v, π)` (top level not
counted, no memoisation): scan the lower-rank neighbours `w_1, w_2, …` of `v` in increasing rank
order, each call to `w_i` costing `1 + calls w_i`, stopping right after the first `w_i` in the
MIS. -/
def calls (π : Equiv.Perm (Fin n)) (v : Fin n) : ℕ :=
  loopCost ((lowerNbrs G π v).attach.map fun w => (inMIS G π w.1, 1 + calls π w.1))
termination_by (π v : ℕ)
decreasing_by exact ((mem_lowerNbrs G π v w.1).1 w.2).2


end RandomGreedyMIS


