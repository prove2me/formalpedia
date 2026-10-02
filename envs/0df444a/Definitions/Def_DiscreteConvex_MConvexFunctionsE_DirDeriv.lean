-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_DirDeriv
-- name    : DiscreteConvex_MConvexFunctionsE_DirDeriv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:05:33.259416+00:00
-- url     : https://prove2.me/theorems/dc3a3f69-dbac-479c-bb4e-6dbf684d51a2
-- title:
--   DirDeriv
-- statement:
--   The directional derivative $f'(x;d) = \inf_{t>0}(f(x+td)-f(x))/t$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Eq. (3.24)-(3.25)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Eq. (3.24)-(3.25)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_PosScalarMul

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The directional derivative `f'(x;d) = inf_{t>0}(f(x+td)-f(x))/t`. -/
noncomputable def DirDeriv (f : (V → ℝ) → WithTop ℝ) (x d : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ t : ℝ, 0 < t ∧
    L = PosScalarMul (1 / t) (f (fun v => x v + t * d v) - f x)}

end DiscreteConvex.MConvexFunctionsE


