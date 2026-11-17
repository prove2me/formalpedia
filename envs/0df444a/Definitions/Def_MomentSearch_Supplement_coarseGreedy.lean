-- Prove2me | Definitions.Def_MomentSearch_Supplement_coarseGreedy
-- name    : MomentSearch_Supplement_coarseGreedy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:30:02.931573+00:00
-- url     : https://prove2.me/theorems/2280fb1f-7812-469f-9237-0699b222d5f2
-- title:
--   $\pi$-medians, standard binary search and the Coarse Greedy strategy
-- statement:
--   For an interval $I=\{a,\dots,b\}$ of $[n]_0$ with $\pi(I)>0$, a **$\pi$-median** is a vertex $m\in I$ with
--   $$\pi(\{a,\dots,m-1\})\le\frac{\pi(I)}2,\qquad \pi(\{m+1,\dots,b\})\le\frac{\pi(I)}2 .$$
--   A **median-selection rule** for $\pi$ assigns to every interval of positive $\pi$-mass one of its $\pi$-medians.
--
--   **Standard binary search** on $\{a,\dots,b\}$ identifies a singleton without a query and otherwise queries the middle vertex $\lfloor(a+b)/2\rfloor$ and recurses on the nonempty sides.
--
--   **Coarse Greedy** with nominal distribution $\pi\in\Delta_n$ and parameter $\varepsilon\in(0,1]$ starts with $I=[n]_0$ and performs at most $h=\lceil\varepsilon\log_2 n\rceil$ median queries with respect to $\pi$ along each branch. After each query it terminates on equality or continues on the side containing the target, and it terminates whenever the remaining interval is a singleton. After $h$ median queries, or earlier if $\pi(I)=0$, it finishes by standard binary search on the remaining interval, independently of $\pi$. The result is a correct deterministic search strategy on $[n]_0$.
--
--   This strategy is the paper's main algorithmic tool: it is the upper bound in Theorems 5, 8 and 9.
--
--   **Formalization Note** The paper does not fix which median is queried when several exist, so Coarse Greedy takes a median-selection rule as a parameter, and the theorems quantify over every rule. Interval masses are written over half-open ranges, so an empty side has mass $0$ with no natural-number subtraction. If a rule returned a vertex outside the interval, the construction would fall back to binary search; for a genuine median rule on an interval of positive mass this never happens.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), §2.3, p.6 (PDF p.8): π-median, Algorithm Coarse Greedy

import Mathlib
import Definitions.Def_MomentSearch_SearchTree

namespace MomentSearch.Supplement

open MomentSearch

/-- The `π`-mass `π({a, …, c − 1}) = ∑_{a ≤ t < c} π_t` of the half-open interval `[a, c)` of
`[n]₀` (arXiv:2611.04559, held version, §2.2–2.3, p.6 (PDF p.8)).

**Formalization Note.** Half-open, so that the empty interval `{a, …, m − 1}` for `m = a` has
mass `0` without natural-number subtraction: `π({a, …, b}) = massIco π a (b + 1)`. -/
def massIco {n : ℕ} (π : Fin n → ℝ) (a c : ℕ) : ℝ :=
  ∑ t : Fin n, if a ≤ (t : ℕ) ∧ (t : ℕ) < c then π t else 0

/-- `m` is a `π`-median of the interval `I = {a, …, b}` (Megow, Stein, Verschae,
*Distributionally Robust Search: The Power of Information and the Limits of Moments*,
arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.3, p.6 (PDF p.8)):
`m ∈ I`, `π({a, …, m − 1}) ≤ π(I)/2` and `π({m + 1, …, b}) ≤ π(I)/2`. -/
def IsMedian {n : ℕ} (π : Fin n → ℝ) (a b m : ℕ) : Prop :=
  a ≤ m ∧ m ≤ b ∧ massIco π a m ≤ massIco π a (b + 1) / 2 ∧
    massIco π (m + 1) (b + 1) ≤ massIco π a (b + 1) / 2

/-- A median-selection rule for `π`: a function `med` returning, for every interval
`{a, …, b} ⊆ [n]₀` with `π({a, …, b}) > 0`, a `π`-median `med a b` of it
(arXiv:2611.04559, held version, §2.3, p.6 (PDF p.8): "Such a vertex always exists").

**Formalization Note.** The paper does not say which median Coarse Greedy queries when several
exist; its theorems hold for every choice, so Coarse Greedy is parametrised by such a rule and
the theorems quantify over all of them. -/
def IsMedianRule {n : ℕ} (π : Fin n → ℝ) (med : ℕ → ℕ → ℕ) : Prop :=
  ∀ a b : ℕ, a ≤ b → b < n → 0 < massIco π a (b + 1) → IsMedian π a b (med a b)

/-- Standard binary search on the interval `{a, …, b}`: on a singleton interval the target is
identified without a query; otherwise query the middle vertex `⌊(a + b)/2⌋` and recurse on the
nonempty sides (arXiv:2611.04559, held version, §2.3, p.6 (PDF p.8): "standard binary search on
the remaining interval, independently of the distributional information"). -/
def binarySearchTree : (a b : ℕ) → a ≤ b → SearchTree a b
  | a, b, hab =>
    if h : a = b then h ▸ SearchTree.leaf a
    else
      SearchTree.node ((a + b) / 2) (by omega) (by omega) (by omega)
        (fun _ => binarySearchTree a ((a + b) / 2 - 1) (by omega))
        (fun _ => binarySearchTree ((a + b) / 2 + 1) b (by omega))
termination_by a b => b - a
decreasing_by all_goals omega

/-- The recursion of Coarse Greedy on the interval `{a, …, b}` after `j` median queries on the
current branch, with median budget `h` (arXiv:2611.04559, held version, §2.3, p.6 (PDF p.8)).

* Singleton interval: the target is identified, no query.
* Fewer than `h` median queries so far and `π({a, …, b}) > 0`: query the median `med a b`,
  terminate on equality, continue on the nonempty side containing the target with `j + 1`.
* Otherwise (after `h` median queries, or earlier if `π(I) = 0`): standard binary search.

**Formalization Note.** If `med a b` were outside `{a, …, b}` the step falls back to binary
search; under `IsMedianRule` this never happens on an interval of positive mass. -/
noncomputable def coarseGreedyAux {n : ℕ} (π : Fin n → ℝ) (med : ℕ → ℕ → ℕ) (h : ℕ) :
    (j a b : ℕ) → a ≤ b → SearchTree a b
  | j, a, b, hab =>
    if hEq : a = b then hEq ▸ SearchTree.leaf a
    else if hm : j < h ∧ 0 < massIco π a (b + 1) ∧ a ≤ med a b ∧ med a b ≤ b then
      SearchTree.node (med a b) hm.2.2.1 hm.2.2.2 (by omega)
        (fun _ => coarseGreedyAux π med h (j + 1) a (med a b - 1) (by omega))
        (fun _ => coarseGreedyAux π med h (j + 1) (med a b + 1) b (by omega))
    else binarySearchTree a b hab
termination_by _ a b => b - a
decreasing_by all_goals omega

/-- **Coarse Greedy** with nominal distribution `π ∈ Δ_n`, parameter `ε ∈ (0, 1]` and
median-selection rule `med` (Megow, Stein, Verschae, *Distributionally Robust Search: The Power
of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…),
§2.3, p.6 (PDF p.8)): starting from `I = [n]₀`, perform at most `h := ⌈ε log₂ n⌉` median
queries with respect to `π`, terminating on equality or on a singleton interval, and continuing
on the side containing the target; after `h` median queries, or earlier if `π(I) = 0`, finish by
standard binary search on the remaining interval.

**Formalization Note.** `log` is base 2 (§2.1). The result is a `Strategy n`, i.e. a correct
deterministic search tree on `{0, …, n − 1}`; the statements using it assume `n ≥ 2`. -/
noncomputable def coarseGreedy {n : ℕ} (π : Fin n → ℝ) (ε : ℝ) (med : ℕ → ℕ → ℕ) :
    Strategy n :=
  coarseGreedyAux π med ⌈ε * Real.logb 2 n⌉₊ 0 0 (n - 1) (Nat.zero_le _)

end MomentSearch.Supplement


