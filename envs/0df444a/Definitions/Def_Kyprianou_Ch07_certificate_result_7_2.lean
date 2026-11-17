-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_2
-- name    : Kyprianou_Ch07_certificate_result_7_2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:48:12.234195+00:00
-- url     : https://prove2.me/theorems/9cda688a-a311-4f05-9610-8d0e2fc75df9
-- title:
--   Full quantified certificate for driftingOscillatingLevyMeasureCriterion
-- statement:
--   Source-quantified exact proposition of the amended theorem 7.2, including its explicitly documented zero-process exception.
-- source:
--   Kyprianou (2006), first edition, Theorem 7.2(i)–(iii), printed p.183, Windows Ky.pdf sheet 97 (original single-page PDF p.192). The author omits the proof.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
import Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of driftingOscillatingLevyMeasureCriterion. -/
def certificate_result_7_2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi),
    (((positiveMeanPart P X < negativeMeanPart P X) ∨
       (HasUndefinedLevyMean P X ∧ negativeDriftTailTest Pi < ⊤) →
       DriftsToNegInfinity P X) ∧
     ((negativeMeanPart P X < positiveMeanPart P X) ∨
       (HasUndefinedLevyMean P X ∧ positiveDriftTailTest Pi < ⊤) →
       DriftsToPosInfinity P X) ∧
     (((positiveMeanPart P X = negativeMeanPart P X ∧
        positiveMeanPart P X < ⊤) ∨
       (HasUndefinedLevyMean P X ∧
        negativeDriftTailTest Pi = ⊤ ∧
        positiveDriftTailTest Pi = ⊤)) →
       IsNontrivialLevyProcess P X →
       OscillatesAtInfinity P X))

end Kyprianou.Ch07


