-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_SeparablePerturbInfConvR
-- name    : DiscreteConvex_LConvexFunctionsC_SeparablePerturbInfConvR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:22.598977+00:00
-- url     : https://prove2.me/theorems/fc951b01-2c34-43f9-88c9-97eded73f5ef
-- title:
--   SeparablePerturbInfConvR
-- statement:
--   The infimal convolution of $g$ with a separable convex function, Eq. (7.33).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.193, Eq. (7.33).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.193, Eq. (7.33)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The infimal convolution of `g` with a separable convex function, Eq. (7.33). -/
noncomputable def SeparablePerturbInfConvR (g : (V → ℝ) → WithTop ℝ) (psi : V → ℝ → WithTop ℝ)
    (p : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ q : V → ℝ, L = g q + ∑ v, psi v (p v - q v)}

end DiscreteConvex.LConvexFunctionsC


