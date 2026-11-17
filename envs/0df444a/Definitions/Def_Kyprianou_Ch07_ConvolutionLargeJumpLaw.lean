-- Prove2me | Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
-- name    : Kyprianou_Ch07_ConvolutionLargeJumpLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:48:28.53179+00:00
-- url     : https://prove2.me/theorems/49990ac4-67ba-4a4c-9f46-31e4d4e0e1a1
-- title:
--   Convolution powers and normalised large ladder-height jumps
-- statement:
--   Defines the convolution of two measures on the reals via the addition pushforward of their product measure, its iterated n-fold convolution, and the probability law of ladder-height jumps conditioned on being larger than one, obtained by restriction and normalisation. The latter applies when the original jump measure has positive, finite mass above one.
-- source:
--   Kyprianou (2006), section 7.6 and Lemma 7.13, printed p.200, Windows Ky.pdf sheet 105 (single-page p.209).

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Convolution of two real distributions as the pushforward of their
product law by addition. -/
noncomputable def sumConvolution
    (mu nu : Measure Real) : Measure Real :=
  Measure.map (fun z : Real × Real => z.1 + z.2) (mu.prod nu)

/-- The n-fold convolution of a measure with itself, with zero-fold
convolution the Dirac mass at zero. -/
noncomputable def convolutionPower
    (mu : Measure Real) : Nat → Measure Real
  | 0 => Measure.dirac (0 : Real)
  | n + 1 => sumConvolution (convolutionPower mu n) mu

/-- The Lévy ladder-height jump measure conditioned on a jump above one.
Only used when its normalising mass is finite and positive. -/
noncomputable def largeJumpNormalisedLaw
    (PiH : Measure Real) : Measure Real :=
  Measure.withDensity (PiH.restrict (Set.Ioi (1 : Real)))
    (fun _ => (PiH (Set.Ioi (1 : Real)))⁻¹)

end Kyprianou.Ch07


