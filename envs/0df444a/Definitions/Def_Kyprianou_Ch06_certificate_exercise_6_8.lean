-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_8
-- name    : Kyprianou_Ch06_certificate_exercise_6_8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:27:38.422942+00:00
-- url     : https://prove2.me/theorems/b842c777-5217-4e96-ac75-24d4294582bf
-- title:
--   Full quantified certificate for exercise:6.8
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Exercise 6.8, printed p. 177; two-up PDF p. 94.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from spitzerTwoRegularityCriteria. -/
def certificate_exercise_6_8 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : IsRealLevyProcess P X)
    (hNotSubordinator : ¬ IsSubordinatorProcess P X),
    (IsRegularFor P X 0 (Set.Ioi 0) ↔
      PositiveOccupationDiverges P X) ∧
    (IsRegularFor P X 0 (Set.Ici 0) ↔
      NonnegativeOccupationDiverges P X)

end Kyprianou.Ch06


