-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_LiftedFunction
-- name    : DiscreteConvex_MConvexFunctionsD_LiftedFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:47:59.244995+00:00
-- url     : https://prove2.me/theorems/9a6f75f0-b12a-4df1-9f65-2098e91d36c9
-- title:
--   LiftedFunction
-- statement:
--   The lift $\tilde f$ of $f$ to $\tilde V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def LiftedFunction (f : (V → ℤ) → WithTop ℝ) : (Option V → ℤ) → WithTop ℝ :=
  fun x => if x none = -(∑ v : V, x (some v)) then f (fun v => x (some v)) else ⊤

end DiscreteConvex.MConvexFunctionsD


