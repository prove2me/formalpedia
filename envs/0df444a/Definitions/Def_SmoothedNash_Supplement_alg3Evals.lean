-- Prove2me | Definitions.Def_SmoothedNash_Supplement_alg3Evals
-- name    : SmoothedNash_Supplement_alg3Evals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:01:03.558545+00:00
-- url     : https://prove2.me/theorems/0d7d37c1-40fe-4a1e-99d2-6e9c0d405d18
-- title:
--   Number of evaluations of $F$ by Algorithm 3
-- statement:
--   The number of evaluations of $F$ made by Algorithm 3 is
--   $$
--   \sum_{k=1}^{K} \sum_{x \in D_{k-1}} |C(x,k)|,
--   $$
--   one evaluation for each pair of a parent $x \in D_{k-1}$ and a candidate $y \in C(x,k)$. This is the quantity bounded in the proof of Theorem 3.3.
--
--   **Formalization Note** A candidate shared by two parents is counted twice, so this count dominates the number of distinct evaluation points.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 3, p.21, and proof of Theorem 3.3, pp.22–23

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_alg3Candidates
import Definitions.Def_SmoothedNash_Supplement_alg3Level
import Definitions.Def_SmoothedNash_Supplement_alg3Depth
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The number of evaluations of `F` made by Algorithm 3 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Algorithm 3, p.21, and the
count bounded in the proof of Theorem 3.3, p.23): one evaluation per pair (parent `x ∈ D_{k−1}`,
candidate `y ∈ C(x, k)`), summed over `k = 1, …, K`:
`∑_{k=1}^{K} ∑_{x ∈ D_{k−1}} |C(x, k)|`.

**Formalization Note** This counts a candidate shared by two parents twice, so it dominates the number
of distinct evaluation points. -/
noncomputable def alg3Evals {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L1 ε : ℝ) : ℕ :=
  ∑ k ∈ Finset.range (alg3Depth L1 ε), ∑ i ∈ alg3Level F L1 k, (alg3Candidates n (k + 1) i).card

end SmoothedNash.Supplement


