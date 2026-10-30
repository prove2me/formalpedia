-- Prove2me | Definitions.Def_JailletLu_LP4Feasible
-- name    : JailletLu_LP4Feasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:17:53.699984+00:00
-- url     : https://prove2.me/theorems/5c643cb4-f6fa-4b7e-b310-bf24e040b1dd
-- title:
--   Feasible points of LP (4)
-- statement:
--   Let $A$ be a finite set of advertisers, $I$ a finite set of impression types, $E\subseteq A\times I$ the edge set of the bipartite graph ($a\sim i$ when $(a,i)\in E$), $r_i$ the arrival rate of type $i$ and $n$ the number of requests. A vector $f=(f_{a,i})_{a\in A,i\in I}$ is **feasible for LP (4)** when it vanishes off $E$ and
--   $$
--   \sum_{i\sim a}f_{a,i}\le 1\ \ (a\in A),\qquad \sum_{a\sim i}f_{a,i}\le r_i\ \ (i\in I),\qquad \sum_{i\sim a}(2f_{a,i}-r_i)^+\le 1-\ln 2+\tfrac1n\ \ (a\in A),\qquad f_e\ge 0\ \ (e\in E).
--   $$
--   LP (4) maximizes $\sum_{a,i}f_{a,i}$ over these points; its third constraint is the one that Lemma 8 (from Manshadi, Oveis Gharan and Saberi) shows the offline optimum satisfies, and it bounds the expected number of singleton lists in the online algorithm.
--
--   **Formalization Note** Only feasibility is encoded, not optimality. For $n=0$, Lean reads $1/n$ as $0$; every theorem of the mission assumes $n\ge 311$.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.1, p. 13, LP (4)

import Mathlib

namespace JailletLu

/-- **Feasibility for LP (4).**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.1, p. 13, LP (4) (with the edge set E of the bipartite graph of §2).

`LP4Feasible E r n f` says that the edge flow `f a i` (advertiser `a`, impression type `i`) is a
feasible point of LP (4) with parameter `n` (the number of arrivals):
1. `f a i ≥ 0`, and `f a i = 0` when `(a, i)` is not an edge (the flow lives on `E`);
2. `Σ_{i∼a} f_{a,i} ≤ 1` for every advertiser `a`;
3. `Σ_{a∼i} f_{a,i} ≤ r_i` for every impression type `i`;
4. `Σ_{i∼a} (2 f_{a,i} − r_i)^+ ≤ 1 − ln 2 + 1/n` for every advertiser `a`.

**Formalization Note.** Only feasibility is encoded, not optimality: none of the statements of the
mission uses optimality. Sums over `i ∼ a` are sums over all `i` because `f` vanishes off `E`. For
`n = 0` the term `1/n` is Lean's `0`; every theorem of the mission assumes `n ≥ 311`. -/
def LP4Feasible {A I : Type*} [Fintype A] [Fintype I] (E : Set (A × I)) (r : I → ℝ) (n : ℕ)
    (f : A → I → ℝ) : Prop :=
  (∀ a i, 0 ≤ f a i) ∧ (∀ a i, (a, i) ∉ E → f a i = 0) ∧
  (∀ a, ∑ i, f a i ≤ 1) ∧ (∀ i, ∑ a, f a i ≤ r i) ∧
  (∀ a, ∑ i, max (2 * f a i - r i) 0 ≤ 1 - Real.log 2 + 1 / (n : ℝ))

end JailletLu


