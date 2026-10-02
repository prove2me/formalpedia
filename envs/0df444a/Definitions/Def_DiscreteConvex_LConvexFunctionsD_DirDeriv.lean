-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_DirDeriv
-- name    : DiscreteConvex_LConvexFunctionsD_DirDeriv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:45.971766+00:00
-- url     : https://prove2.me/theorems/26dc19e7-b6d2-4da2-93f8-4139c5c18c29
-- title:
--   DirDeriv
-- statement:
--   The directional derivative $g'(p;d) = \inf_{t>0}(g(p+td)-g(p))/t$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Eq. (3.24)-(3.25)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Eq. (3.24)-(3.25)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosScalarMul

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The directional derivative `g'(p;d) = inf_{t>0}(g(p+td)-g(p))/t`. -/
noncomputable def DirDeriv (g : (V → ℝ) → WithTop ℝ) (p d : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ t : ℝ, 0 < t ∧
    L = PosScalarMul (1 / t) (g (fun v => p v + t * d v) - g p)}

end DiscreteConvex.LConvexFunctionsD


