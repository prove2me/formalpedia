-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_LiftedFunctionLR
-- name    : DiscreteConvex_ConjugacyDualityB_LiftedFunctionLR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:52.713189+00:00
-- url     : https://prove2.me/theorems/ac5c5bdc-854f-4de1-8d16-b1239938845c
-- title:
--   LiftedFunctionLR
-- statement:
--   The lift of a real-domain function to one extra real coordinate, L-side convention.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, real-variable analogue

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift of a real-domain function to one extra real coordinate, L-side convention. -/
def LiftedFunctionLR (g : (V → ℝ) → WithTop ℝ) : (Option V → ℝ) → WithTop ℝ :=
  fun x => g (fun v => x (some v) - x none)

end DiscreteConvex.ConjugacyDualityB


