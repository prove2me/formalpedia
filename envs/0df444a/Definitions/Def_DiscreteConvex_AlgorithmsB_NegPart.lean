-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_NegPart
-- name    : DiscreteConvex_AlgorithmsB_NegPart
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:49:59.170977+00:00
-- url     : https://prove2.me/theorems/3e07d895-f376-4d55-827b-3326f02fd14b
-- title:
--   NegPart
-- statement:
--   $x^-(v)=\min(0,x(v))$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, Eq. (10.10).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, Eq. (10.10)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `x⁻(v) = min(0,x(v))`. -/
def NegPart (x : V → ℝ) (v : V) : ℝ := min 0 (x v)

end DiscreteConvex.AlgorithmsB


