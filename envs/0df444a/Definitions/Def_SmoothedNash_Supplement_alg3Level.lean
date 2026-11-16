-- Prove2me | Definitions.Def_SmoothedNash_Supplement_alg3Level
-- name    : SmoothedNash_Supplement_alg3Level
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:00:12.164685+00:00
-- url     : https://prove2.me/theorems/339f7f9c-861f-442c-8440-b9eeda5ee844
-- title:
--   The sets $D_k$ of Algorithm 3 (tree search and pruning)
-- statement:
--   Algorithm 3 builds sets $D_0, D_1, \dots$ of grid points: $D_0 = \{0\}$ and, for $k \ge 1$,
--   $$
--   D_k = \bigcup_{x \in D_{k-1}} \{\, y \in C(x,k) : \|F(y) - y\| \le r_k (1 + L_1) \,\}, \qquad r_k = 2^{-k}.
--   $$
--   The algorithm outputs any point of $D_K$.
--
--   **Formalization Note** Points are stored as level-$k$ integer vectors; a point produced from two parents is kept once.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 3, lines 1–9, p.21

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_latticePt
import Definitions.Def_SmoothedNash_Supplement_alg3Candidates
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The sets `D_k` of Algorithm 3 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Algorithm 3, lines 1–9, p.21), as finite sets of
level-`k` integer vectors: `D_0 = {0}`, and `D_k` collects, over all parents `x ∈ D_{k−1}`, every
candidate `y ∈ C(x, k)` with `‖F(y) − y‖ ≤ r_k (1 + L1)`, `r_k = 2^{−k}`.

**Formalization Note** `D_k` is a set: a point produced from two parents is kept once (the union
`biUnion`). The level-`k` point of vector `j` is `latticePt n k j`. -/
noncomputable def alg3Level {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L1 : ℝ) : ℕ → Finset (Fin n → ℤ)
  | 0 => {0}
  | k + 1 => by
    classical
    exact (alg3Level F L1 k).biUnion fun i =>
      (alg3Candidates n (k + 1) i).filter fun j =>
        ‖F (latticePt n (k + 1) j) - latticePt n (k + 1) j‖ ≤ ((2 : ℝ) ^ (k + 1))⁻¹ * (1 + L1)

end SmoothedNash.Supplement


