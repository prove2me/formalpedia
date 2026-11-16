-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_result_6_8
-- name    : Kyprianou_Ch06_certificate_result_6_8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:19:42.708278+00:00
-- url     : https://prove2.me/theorems/7057d93b-c718-4028-a681-c11188d46d43
-- title:
--   Full quantified certificate for result:6.8
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Theorem 6.8, printed p. 146; physical PDF p. 78.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from maximumOccupationCoefficientCriterion. -/
def certificate_result_6_8 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal) (a : NNReal)
    (hX : IsRealLevyProcess P X)
    (hClosedRegular : IsRegularFor P X 0 (Set.Ici 0))
    (hL : IsContinuousLocalTimeAtMaximum P F X L)
    (hOccupation : ∀ᵐ omega ∂P, ∀ t : NNReal,
      (∫ s in Set.Icc (0 : NNReal) t,
        if X s omega = runningMaximum X s omega
        then (1 : Real) else 0 ∂(Measure.map Real.toNNReal (volume.restrict (Set.Ici (0 : Real))))) =
          (a : Real) * (L t omega : Real)),
    (0 < a ↔
      ((∀ᵐ omega ∂P, ∀ T : NNReal,
          ∃ C : Real, 0 ≤ C ∧
            ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
              StrictMono times → times (Fin.last n) ≤ T →
              (∑ i : Fin n,
                |X (times i.succ) omega -
                  X (times i.castSucc) omega|) ≤ C) ∧
        IsIrregularFor P X 0 (Set.Iio 0)))

end Kyprianou.Ch06


