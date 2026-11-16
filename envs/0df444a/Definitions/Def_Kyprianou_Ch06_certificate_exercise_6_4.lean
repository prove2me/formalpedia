-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_4
-- name    : Kyprianou_Ch06_certificate_exercise_6_4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:25:38.782208+00:00
-- url     : https://prove2.me/theorems/4dd62324-ee23-4690-8e0a-bbebe7235118
-- title:
--   Full quantified certificate for exercise:6.4
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Exercise 6.4, printed p. 175; two-up PDF p. 93.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from compoundPoissonOfBothExtremalOccupations. -/
def certificate_exercise_6_4 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : IsRealLevyProcess P X)
    (hOccupations :
      P {omega |
        (∫⁻ t : NNReal,
          if X t omega = runningMaximum X t omega
          then (1 : ENNReal) else 0 ∂(Measure.map Real.toNNReal (volume.restrict (Set.Ici (0 : Real))))) > 0 ∧
        (∫⁻ t : NNReal,
          if X t omega =
            sInf ((fun u : NNReal => X u omega) '' Set.Icc 0 t)
          then (1 : ENNReal) else 0 ∂(Measure.map Real.toNNReal (volume.restrict (Set.Ici (0 : Real))))) > 0} = 1),
    IsCompoundPoissonProcess P X

end Kyprianou.Ch06


