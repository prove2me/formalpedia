-- Prove2me | Definitions.Def_IntMul_CarryProduct
-- name    : IntMul_CarryProduct
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T13:07:00.017005+00:00
-- url     : https://prove2.me/theorems/542ccc06-dd48-4172-a3f8-70ebc488f128
-- title:
--   Explicit convolution-coefficient caller frame for physical product recovery
-- statement:
--   Let $B>0$ and let $x,y$ be finite binary operand words. If $m_x,m_y$ are their retained base-$2^B$ block counts, use coefficient width $N=2B+\lceil\log_2\min(m_x,m_y)\rceil$ (with the natural-number ceiling-log convention at zero). The prepared caller frame contains the padded coefficient words of the product digit polynomial, a zero saved carry of width $N$, and explicit width descriptors. The actual machine is the fixed fifteen-tape physical carry/output machine; it introduces no new transition table. The frame does not assert that generating or loading coefficients is free. Correctness and the complete physical execution clock are separate theorem obligations.
-- source:
--   Explicit prepared coefficient and zero-carry frame connecting actual carry execution with accepted convolution product recovery. Written by Codex.

import Definitions.Def_IntMul_CarryOutput
import Definitions.Def_IntMul_CarryNormalization
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.CarryProduct

/-- The accepted convolution/carry width, large enough for every coefficient
and every carry. It is an explicit prepared descriptor obligation. -/
noncomputable def coefficientWidth (B : ℕ) (x y : List Bool) : ℕ :=
  2*B+Nat.clog 2 (min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y))

noncomputable def coefficientWords (B : ℕ) (x y : List Bool) : List (List Bool) :=
  (CarryNormalization.coefficients B x y).map (bin (coefficientWidth B x y))

noncomputable abbrev machine : MultitapeTM := CarryOutput.machine

/-- Coefficients are already physically present at the retained root cursor.
This frame never asserts that coefficient generation or loading is free. -/
noncomputable def initialFrame (pre x y z l : List Bool) : machine.Cfg :=
  CarryOutput.initialFrame pre (coefficientWords (CarryStep.blockSize z) x y) []
    (bin (coefficientWidth (CarryStep.blockSize z) x y) 0) z l

noncomputable def finalFrame (pre x y z l : List Bool) : machine.Cfg :=
  CarryOutput.finalFrame pre (coefficientWords (CarryStep.blockSize z) x y) []
    (bin (coefficientWidth (CarryStep.blockSize z) x y) 0) z l

end IntMul.CarryProduct


