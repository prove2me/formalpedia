-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_14
-- name    : Kyprianou_Ch07_certificate_result_7_14
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:51:06.077572+00:00
-- url     : https://prove2.me/theorems/36c0d037-6dbb-4d39-8584-d0f333f16079
-- title:
--   Full quantified certificate for kestenBoundSubexponentialConvolution
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), Lemma 7.14, printed p.201, Windows Ky.pdf landscape sheet 106 (original single-page PDF p.210).

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of kestenBoundSubexponentialConvolution. -/
def certificate_result_7_14 : Prop :=
  ∀ (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConvolutionAsymptotics : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))),
    ∀ epsilon : Real, 0 < epsilon →
      ∃ C : Real, 0 < C ∧
        ∀ n : Nat, 1 ≤ n →
          ∀ x : Real, 0 < x →
            ((convolutionPower G n) (Set.Ioi x)).toReal /
              (G (Set.Ioi x)).toReal ≤ C * (1 + epsilon) ^ n

end Kyprianou.Ch07


