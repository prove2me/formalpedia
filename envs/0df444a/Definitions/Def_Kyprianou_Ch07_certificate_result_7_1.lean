-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_1
-- name    : Kyprianou_Ch07_certificate_result_7_1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:45:14.649197+00:00
-- url     : https://prove2.me/theorems/a38adbd3-307b-4d88-b37b-f4e2532ac64a
-- title:
--   Full quantified certificate for driftingOscillatingIntegralTrichotomy
-- statement:
--   Source-quantified exact proposition of the amended theorem 7.1, including its explicitly documented zero-process exception.
-- source:
--   Kyprianou (2006), first edition, Theorem 7.1(i)–(iii), printed page 180, Windows Ky.pdf landscape sheet 95 (original single-page PDF p.189).

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of driftingOscillatingIntegralTrichotomy. -/
def certificate_result_7_1 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X),
    ((nonnegativeSignIntegral P X < ⊤ →
      DriftsToNegInfinity P X) ∧
     (nonpositiveSignIntegral P X < ⊤ →
      DriftsToPosInfinity P X) ∧
     (nonnegativeSignIntegral P X = ⊤ →
      nonpositiveSignIntegral P X = ⊤ →
      IsNontrivialLevyProcess P X →
      OscillatesAtInfinity P X))

end Kyprianou.Ch07


