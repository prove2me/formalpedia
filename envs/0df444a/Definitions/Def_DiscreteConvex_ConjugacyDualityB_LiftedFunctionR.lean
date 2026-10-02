-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_LiftedFunctionR
-- name    : DiscreteConvex_ConjugacyDualityB_LiftedFunctionR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:39.104012+00:00
-- url     : https://prove2.me/theorems/5fc04e96-9ca3-415f-a455-d8bcb462e008
-- title:
--   LiftedFunctionR
-- statement:
--   The lift of a real-domain function to one extra real coordinate.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162, real-variable analogue

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift of a real-domain function to one extra real coordinate. -/
noncomputable def LiftedFunctionR (f : (V → ℝ) → WithTop ℝ) : (Option V → ℝ) → WithTop ℝ :=
  fun x => if x none = -(∑ v : V, x (some v)) then f (fun v => x (some v)) else ⊤

end DiscreteConvex.ConjugacyDualityB


