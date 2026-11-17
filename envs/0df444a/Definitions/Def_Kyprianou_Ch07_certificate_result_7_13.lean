-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_13
-- name    : Kyprianou_Ch07_certificate_result_7_13
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:50:36.251518+00:00
-- url     : https://prove2.me/theorems/10f1e5b4-afb9-422d-ad7d-0be56484b703
-- title:
--   Full quantified certificate for regularlyVaryingConvolutionTails
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), Lemma 7.13, printed page 200, Windows Ky.pdf sheet 105 (original single-page PDF p.209).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of regularlyVaryingConvolutionTails. -/
def certificate_result_7_13 : Prop :=
  ∀ (PiH : Measure Real) (alpha : Real)
    (hAlpha : 0 < alpha)
    (hPositiveJumpSupport : PiH (Set.Iic (0 : Real)) = 0)
    (hLargeFinite : PiH (Set.Ioi (1 : Real)) < ⊤)
    (hLargePositive : 0 < PiH (Set.Ioi (1 : Real)))
    (hRegular : Kyprianou.Ch05.RegularlyVaryingAtInfinity
      (fun x : Real => (PiH (Set.Ioi x)).toReal) (-alpha)),
    let nu : Measure Real := largeJumpNormalisedLaw PiH
    ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((convolutionPower nu n) (Set.Ioi x)).toReal /
          ((n : Real) * (nu (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))

end Kyprianou.Ch07


