-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_RationalHeight
-- name    : InfoLossLAR_Native_AFT_RationalHeight
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T02:25:00.287546+00:00
-- url     : https://prove2.me/theorems/6b8d2547-6717-44dc-8311-6e6502af3e05
-- title:
--   Binary height bounds for rational arithmetic
-- statement:
--   For a rational number $r$ and an integer $b\ge 0$, $\operatorname{HeightBound}(r,b)$ means that the absolute numerator and positive denominator of $r$ in reduced form are both at most $2^b$. This predicate tracks operand sizes in the constructive Gaussian affine sampler.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/RationalHeight.lean, lines 7–9; Lean 4.33.1 migration snapshot b36d23aa37fbb4858aa450c39ac4667286ed70f7f49a16d03f77dbe27782e103

import Mathlib


/-! # Explicit binary height bounds for executable rational arithmetic -/
namespace AFT.RationalNumerics
open scoped BigOperators

/-- The reduced numerator and denominator each fit below a binary power. -/
def HeightBound (value : ℚ) (bits : ℕ) : Prop :=
  value.num.natAbs ≤ 2^bits ∧ value.den ≤ 2^bits

namespace HeightBound






























end HeightBound
end AFT.RationalNumerics


