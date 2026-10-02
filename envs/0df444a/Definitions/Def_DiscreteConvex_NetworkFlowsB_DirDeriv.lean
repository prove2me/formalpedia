-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_DirDeriv
-- name    : DiscreteConvex_NetworkFlowsB_DirDeriv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:30.116988+00:00
-- url     : https://prove2.me/theorems/ffbdd2cb-1558-44a9-bde1-ac0f5e4b3a69
-- title:
--   DirDeriv
-- statement:
--   The directional derivative $f'(x;d)=\inf_{t>0}(f(x+td)-f(x))/t$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79, Eq. (3.24), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79, Eq. (3.24), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_PosScalarMul

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The directional derivative `f'(x;d) = inf_{t>0} (f(x+td)-f(x))/t`. -/
noncomputable def DirDeriv (f : (V → ℝ) → WithTop ℝ) (x d : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ t : ℝ, 0 < t ∧
    L = PosScalarMul (1 / t) (f (fun v => x v + t * d v) - f x)}

end DiscreteConvex.NetworkFlowsB


