-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_DirDeriv
-- name    : DiscreteConvex_MConvexFunctionsD_DirDeriv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:50:47.573333+00:00
-- url     : https://prove2.me/theorems/7f3594cd-d257-480e-8b2b-057e5dce0d6a
-- title:
--   DirDeriv
-- statement:
--   The directional derivative $f'(x;d) = \inf_{t>0}(f(x+td)-f(x))/t$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Eq. (3.24)-(3.25)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Eq. (3.24)-(3.25)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosScalarMul

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The directional derivative `f'(x;d) = inf_{t>0} (f(x+td)-f(x))/t`, Eq. (3.24)-adjacent. -/
noncomputable def DirDeriv (f : (V → ℝ) → WithTop ℝ) (x d : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ t : ℝ, 0 < t ∧
    L = PosScalarMul (1 / t) (f (fun v => x v + t * d v) - f x)}

end DiscreteConvex.MConvexFunctionsD


