-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_IsConvexCombOfExtremeBases
-- name    : DiscreteConvex_AlgorithmsB_IsConvexCombOfExtremeBases
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:02:16.570297+00:00
-- url     : https://prove2.me/theorems/76ae478a-efb0-421e-8343-11f82c3fda3d
-- title:
--   IsConvexCombOfExtremeBases
-- statement:
--   $x$ is represented as a convex combination $\sum\lambda_iy_i$ of extreme bases.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, Eq. (10.13).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, Eq. (10.13)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_ExtremeBaseVec

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `x` is represented as a convex combination `Σ λᵢyᵢ` of extreme bases (Eq. (10.13)). -/
def IsConvexCombOfExtremeBases {ι : Type*} [DecidableEq ι] (rho : Finset V → ℤ) (I : Finset ι)
    (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ) (x : V → ℝ) : Prop :=
  (∀ i ∈ I, 0 ≤ lam i) ∧ (∑ i ∈ I, lam i = 1) ∧
    (∀ v, x v = ∑ i ∈ I, lam i * (ExtremeBaseVec rho (L i) v : ℝ))

-- ===== δ-feasible flows and the auxiliary network (§10.2.3) =====

end DiscreteConvex.AlgorithmsB


