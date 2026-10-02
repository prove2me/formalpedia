-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_LiftedFunctionR
-- name    : DiscreteConvex_MConvexFunctionsC_LiftedFunctionR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:49.166996+00:00
-- url     : https://prove2.me/theorems/4f4ba940-4a51-4328-9c68-23e91336b874
-- title:
--   LiftedFunctionR
-- statement:
--   The lift of a real-valued function $g$ to one extra real coordinate.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162, real-variable analogue of Eq. (6.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162, real-variable analogue of Eq. (6.4)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def LiftedFunctionR (g : (V → ℝ) → WithTop ℝ) : (Option V → ℝ) → WithTop ℝ :=
  fun x => if x none = -(∑ v : V, x (some v)) then g (fun v => x (some v)) else ⊤

end DiscreteConvex.MConvexFunctionsC


