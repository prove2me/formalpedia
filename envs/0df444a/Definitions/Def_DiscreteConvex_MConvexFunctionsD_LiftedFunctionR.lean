-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_LiftedFunctionR
-- name    : DiscreteConvex_MConvexFunctionsD_LiftedFunctionR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:47.339879+00:00
-- url     : https://prove2.me/theorems/561cbfaa-cd81-4c1a-82b7-270999b43098
-- title:
--   LiftedFunctionR
-- statement:
--   The lift of a real-valued function to one extra real coordinate.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def LiftedFunctionR (g : (V → ℝ) → WithTop ℝ) : (Option V → ℝ) → WithTop ℝ :=
  fun x => if x none = -(∑ v : V, x (some v)) then g (fun v => x (some v)) else ⊤

end DiscreteConvex.MConvexFunctionsD


