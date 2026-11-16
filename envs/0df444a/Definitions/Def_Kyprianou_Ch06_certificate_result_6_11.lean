-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_result_6_11
-- name    : Kyprianou_Ch06_certificate_result_6_11
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:21:17.903224+00:00
-- url     : https://prove2.me/theorems/a9a7bb61-0247-4e2b-8b1e-8a74c5e1e560
-- title:
--   Full quantified certificate for result:6.11
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Corollary 6.11, printed p. 153; physical PDF p. 82; Theorem 6.8 occupation constant.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from ascendingLadderTimeDrift. -/
def certificate_result_6_11 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal) (a : NNReal)
    (hX : IsRealLevyProcess P X)
    (hL : IsAdmissibleLocalTimeAtMaximum P F X L)
    (hOccupation : ∀ᵐ omega ∂P, ∀ t : NNReal,
      (∫ s in Set.Icc (0 : NNReal) t,
        if X s omega = runningMaximum X s omega
        then (1 : Real) else 0 ∂(Measure.map Real.toNNReal (volume.restrict (Set.Ici (0 : Real))))) =
          (a : Real) * (L t omega : Real)),
    ∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal =>
        (inverseLocalTime L t omega).untopD 0 / t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds a)

end Kyprianou.Ch06


