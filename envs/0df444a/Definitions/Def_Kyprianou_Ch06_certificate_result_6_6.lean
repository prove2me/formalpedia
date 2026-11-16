-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_result_6_6
-- name    : Kyprianou_Ch06_certificate_result_6_6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:18:38.278576+00:00
-- url     : https://prove2.me/theorems/58fc1e3c-a187-404b-bef8-7d5f44beb1af
-- title:
--   Full quantified certificate for result:6.6
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Corollary 6.6, printed p. 144; two-up PDF p. 77.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from onlyCompoundPoissonHasClosedNotOpenRegularity. -/
def certificate_result_6_6 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : IsRealLevyProcess P X)
    (hClosed : IsRegularFor P X 0 (Set.Ici 0))
    (hNotOpen : ¬ IsRegularFor P X 0 (Set.Ioi 0)),
    IsCompoundPoissonProcess P X

end Kyprianou.Ch06


