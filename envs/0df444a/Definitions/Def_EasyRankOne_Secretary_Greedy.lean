-- Prove2me | Definitions.Def_EasyRankOne_Secretary_Greedy
-- name    : EasyRankOne_Secretary_Greedy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:04:52.057484+00:00
-- url     : https://prove2.me/theorems/2e9c61d3-ae5d-484b-a361-8113dbe014f3
-- title:
--   Tie-broken value order, ordered sets and the canonical greedy optimum Greedy(T) (§2.1, §4.1)
-- statement:
--   Let $V$ be a finite ground set carrying a fixed **label order**, $M=(V,\mathcal I)$ a matroid with $M.E=V$, and $v:V\to\mathbb R$ values. The **tie-broken value order** is $f\succ e$ iff $v_f>v_e$, or $v_f=v_e$ and the label of $f$ is larger. For $T\subseteq V$, $\mathrm{Greedy}(T)$ is the output of greedy, which scans $T$ in decreasing tie-broken order and adds each element keeping the set independent; equivalently (p. 5: "an element is selected precisely when the elements preceding it do not span it")
--   $$\mathrm{Greedy}(T)=\{e\in T:\ e\notin \mathrm{cl}(\{f\in T: f\succ e\})\}.$$
--   Loops are never selected; zero-valued nonloops are. The **canonical optimum** is $\mathrm{Greedy}(V)$. An **ordered set** $O$ (§4.1) is a subset of $V$ with its decreasing order; $O-e$ inherits the order and $\mathrm{Greedy}(O)$ is greedy under the order of $O$.
--
--   **Formalization Note.** The label order is the `LinearOrder` of the ground type `α`; `Larger v f e` is $f\succ e$, the lexicographic order on (value, label). `greedyBy M r T` is the closure form above for a scan order `r`; `Greedy M v T := greedyBy M (Larger v) T`. An ordered set is a duplicate-free `List α` listed in decreasing order (first element largest); `ListLarger O f e` is $f\succ e$ in $O$, `O.erase e` is $O-e$, `greedyList M O` is $\mathrm{Greedy}(O)$, and `sortDesc v T` lists a finite set $T$ in decreasing tie-broken order.
-- source:
--   Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, As Easy as Rank One, STOC 2027 submission (manuscript of November 2026, sha256 f74f3f91…), p. 1, footnote 1; p. 5, §2.1; p. 11, §4.1

import Mathlib

/-!
# Tie-broken value order, ordered sets and the canonical greedy optimum

Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, *As Easy as Rank One*, STOC 2027 submission
(manuscript of November 2026, sha256 f74f3f91…), §2.1 p. 5, footnote 1 p. 1, §4.1 p. 11.

"Fix a matroid M = (V, I) with nonnegative values v_e. Ties are broken by a fixed order of element
labels, independent of arrival order; 'larger' and 'smaller' refer to this tie-broken value
order. … let Greedy(T) be the output of greedy, which scans T in decreasing value order and adds
each element that keeps the current set independent. … an element is selected precisely when the
elements preceding it do not span it."

Conventions.
* The ground type `α` carries the label order as its `LinearOrder`; `Larger v f e` is `f ≻ e`:
  `v f > v e`, or `v f = v e` and the label of `f` is larger.
* `greedyBy M r T` is the set of `e ∈ T` not spanned (`Matroid.closure`) by the elements of `T`
  that precede `e` in the scan order `r`; this is the output of the greedy scan (p. 5). Loops are
  never selected, zero-valued nonloops are.
* An **ordered set** (§4.1, p. 11) is a duplicate-free list, listed in decreasing order: its
  first element is its largest. `ListLarger O f e` is `f ≻ e` inside `O`; `O.erase e` is the
  ordered set `O − e` with the inherited order; `greedyList M O` is `Greedy(O)` under the order of
  `O`; `sortDesc v T` is the ordered set of a finite set `T` under the tie-broken value order.
-/

namespace EasyRankOne.Secretary

variable {α : Type*}

/-- `Larger v f e`: `f ≻ e` in the tie-broken value order — a larger value, or an equal value
and a larger label (the label order is the `LinearOrder` of `α`). -/
def Larger [LinearOrder α] (v : α → ℝ) (f e : α) : Prop :=
  toLex (v e, e) < toLex (v f, f)

/-- Greedy with respect to a scan order `r` (`r f e`: `f` is scanned before `e`): the elements
of `T` not spanned by the elements of `T` scanned before them. -/
def greedyBy (M : Matroid α) (r : α → α → Prop) (T : Set α) : Set α :=
  {e | e ∈ T ∧ e ∉ M.closure {f | f ∈ T ∧ r f e}}

/-- `Greedy(T)`: decreasing-value greedy on `T` with ties broken by labels. The canonical
optimum is `Greedy M v Set.univ`. -/
def Greedy [LinearOrder α] (M : Matroid α) (v : α → ℝ) (T : Set α) : Set α :=
  greedyBy M (Larger v) T

/-- In an ordered set `O` (a list in decreasing order), `f ≻ e`: both lie in `O` and `f` comes
first. -/
def ListLarger [DecidableEq α] (O : List α) (f e : α) : Prop :=
  f ∈ O ∧ e ∈ O ∧ O.idxOf f < O.idxOf e

/-- `Greedy(O)` for an ordered set `O`, under the order of `O`. -/
def greedyList [DecidableEq α] (M : Matroid α) (O : List α) : Set α :=
  greedyBy M (ListLarger O) {e | e ∈ O}

/-- The ordered set of a finite set `T` under the tie-broken value order of `v`: `T` listed in
decreasing order. -/
noncomputable def sortDesc [LinearOrder α] (v : α → ℝ) (T : Finset α) : List α :=
  T.toList.mergeSort (fun a b => decide (toLex (v b, b) ≤ toLex (v a, a)))

end EasyRankOne.Secretary


