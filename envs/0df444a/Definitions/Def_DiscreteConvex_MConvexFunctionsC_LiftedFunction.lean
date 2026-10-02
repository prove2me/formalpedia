-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_LiftedFunction
-- name    : DiscreteConvex_MConvexFunctionsC_LiftedFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:18.914384+00:00
-- url     : https://prove2.me/theorems/d4806e31-826a-4506-aef9-d39626f72f4a
-- title:
--   LiftedFunction
-- statement:
--   The lift $\tilde f$ of $f$ to $\tilde V=\{0\}\cup V$ (Eq. (6.4)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def LiftedFunction (f : (V → ℤ) → WithTop ℝ) : (Option V → ℤ) → WithTop ℝ :=
  fun x => if x none = -(∑ v : V, x (some v)) then f (fun v => x (some v)) else ⊤

end DiscreteConvex.MConvexFunctionsC


