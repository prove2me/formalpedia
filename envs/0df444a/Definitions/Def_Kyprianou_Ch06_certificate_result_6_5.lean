-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_result_6_5
-- name    : Kyprianou_Ch06_certificate_result_6_5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:18:10.8952+00:00
-- url     : https://prove2.me/theorems/b88fd940-70b6-4df1-bc8e-9ffcbdbbbc87
-- title:
--   Full quantified certificate for result:6.5
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Theorem 6.5, printed pp. 142–143; two-up PDF pp. 76–77.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from positiveHalfLineRegularityClassification. -/
def certificate_result_6_5 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b d : Real) (sigma2 : NNReal) (nu : Measure Real)
    (hX : IsRealLevyProcess P X)
    (hTriplet : IsLevyKhintchineTriplet P X b sigma2 nu)
    (hDrift : (sigma2 = 0 ∧
      (∫⁻ x in {x : Real | |x| < 1},
        ENNReal.ofReal |x| ∂nu) < ⊤) →
      d = b - ∫ x in {x : Real | |x| < 1}, x ∂nu)
    (hNonCompound : ¬ IsCompoundPoissonProcess P X),
    (IsRegularFor P X 0 (Set.Ioi 0) ↔
      PositiveOccupationDiverges P X) ∧
    (PositiveOccupationDiverges P X ↔
      (¬ (sigma2 = 0 ∧
        (∫⁻ x in {x : Real | |x| < 1},
          ENNReal.ofReal |x| ∂nu) < ⊤)) ∨
      ((sigma2 = 0 ∧
        (∫⁻ x in {x : Real | |x| < 1},
          ENNReal.ofReal |x| ∂nu) < ⊤) ∧ 0 < d) ∨
      ((sigma2 = 0 ∧
        (∫⁻ x in {x : Real | |x| < 1},
          ENNReal.ofReal |x| ∂nu) < ⊤) ∧
        d = 0 ∧
        (∫⁻ x in Set.Ioo (0 : Real) 1,
          (ENNReal.ofReal x) /
            (∫⁻ y in Set.Ioo (0 : Real) x,
              nu (Set.Iio (-y)) ∂volume) ∂nu) = ⊤))

end Kyprianou.Ch06


