-- Prove2me | Definitions.Def_GeomRescale_IsSortedBy
-- name    : GeomRescale_IsSortedBy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:38.232503+00:00
-- url     : https://prove2.me/theorems/ad7f4209-f9da-474f-befc-1470e3043888
-- title:
--   An order sorted by a weight vector
-- statement:
--   An order $v_1, \dots, v_n$ of $V$ is sorted by $w : V \to \mathbb{R}$ if
--
--   $$w(v_1) \le w(v_2) \le \dots \le w(v_n).$$
--
--   This is the order that $\mathrm{GreedyMin}(f, w)$ computes. When $w$ has ties several orders qualify, and every statement of the mission holds for all of them.
--
--   **Formalization Note** An order is a permutation $\sigma$ read as a position map, $v_{i+1} = \sigma^{-1}(i)$, as in the published `SchrijverSFM.Alg.greedy`.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4

import Mathlib

namespace GeomRescale

/-- The order `v₁, …, v_n` given by the position map `σ` satisfies
`w(v₁) ≤ w(v₂) ≤ … ≤ w(v_n)` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4, the order used by `GreedyMin(f, w)`).

**Formalization Note.** An order of `V` is a permutation `σ` read as a position map, `v_i = σ⁻¹(i)`,
as in the published `SchrijverSFM.Alg.greedy`. When `w` has ties several `σ` qualify, and every
statement quantifies over all of them. -/
def IsSortedBy {n : ℕ} (w : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ u v : Fin n, σ u < σ v → w u ≤ w v

end GeomRescale


