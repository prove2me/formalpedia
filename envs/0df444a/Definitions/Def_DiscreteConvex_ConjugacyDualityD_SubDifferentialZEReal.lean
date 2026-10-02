-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_SubDifferentialZEReal
-- name    : DiscreteConvex_ConjugacyDualityD_SubDifferentialZEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:56:20.078154+00:00
-- url     : https://prove2.me/theorems/79babc1f-f92e-428b-afa7-2773223cf6f5
-- title:
--   SubDifferentialZEReal
-- statement:
--   The subdifferential of an `EReal`-valued function at a point.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240-241, Eq. (8.71)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240-241, Eq. (8.71)-adjacent

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The subdifferential of an `EReal`-valued function at a point. -/
def SubDifferentialZEReal (F : (V → ℤ) → EReal) (x0 : V → ℤ) : Set (V → ℤ) :=
  {y : V → ℤ | ∀ x : V → ℤ,
    F x - F x0 ≥ ((∑ i, (y i : ℝ) * ((x i : ℝ) - (x0 i : ℝ)) : ℝ) : EReal)}

end DiscreteConvex.ConjugacyDualityD


