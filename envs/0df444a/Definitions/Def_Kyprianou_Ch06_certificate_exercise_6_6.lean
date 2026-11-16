-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_6
-- name    : Kyprianou_Ch06_certificate_exercise_6_6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:26:45.674508+00:00
-- url     : https://prove2.me/theorems/7773d946-17bd-4640-baf2-6d870b5e349a
-- title:
--   Full quantified certificate for exercise:6.6
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Exercise 6.6(i)–(ii), printed p. 176; two-up PDF p. 93. T=0 boundary correction documented in source issues.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from spectrallyNegativeStablePositivityAndSupremum. -/
def certificate_exercise_6_6 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal)
    (alpha : Real) (kappa : NNReal → Real)
    (hAlpha : 1 < alpha ∧ alpha < 2)
    (hX : IsRealLevyProcess P X)
    (hStable : ∀ (t : NNReal) (lambda : Real), 0 ≤ lambda →
      (∫ omega,
        Real.exp (lambda * X t omega) ∂P) =
        Real.exp ((t : Real) * (lambda ^ alpha)))
    (hL : IsAdmissibleLocalTimeAtMaximum P F X L)
    (hKappa : ∀ (s q : NNReal),
      (∫ omega,
        Real.exp (-((q : Real) *
          (↑((inverseLocalTime L s omega).untopD 0) : Real))) ∂P) =
        Real.exp (-(s : Real) * kappa q)),
    (∃ c : Real, 0 < c ∧
      ∀ q : NNReal, kappa q = c * ((q : Real) ^ (1 / alpha))) ∧
    (∀ t : NNReal, 0 < t →
      P {omega | 0 ≤ X t omega} =
        ENNReal.ofReal (1 / alpha)) ∧
    (∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega,
        Real.exp (-theta * runningMaximum X t omega) ∂P) =
        ∑' n : Nat,
          ((-theta * ((t : Real) ^ (1 / alpha))) ^ n) /
            Real.Gamma (1 + (n : Real) / alpha))

end Kyprianou.Ch06


