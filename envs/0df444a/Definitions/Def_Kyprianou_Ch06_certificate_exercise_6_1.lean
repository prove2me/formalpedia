-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_1
-- name    : Kyprianou_Ch06_certificate_exercise_6_1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:24:22.191336+00:00
-- url     : https://prove2.me/theorems/96a2f96b-6a2a-4a32-85ad-98d87be07832
-- title:
--   Full quantified certificate for exercise:6.1
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Exercise 6.1, printed pp. 174–175; physical PDF pp. 92–93.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from stableExamplesOfBoundedVariationZeroDriftRegularity. -/
def certificate_exercise_6_1 : Prop :=
  ∃ (alpha : Real) (Pboth Ppositive : Measure (NNReal → Real)),
      0 < alpha ∧ alpha < 1 ∧
      IsProbabilityMeasure Pboth ∧
      IsProbabilityMeasure Ppositive ∧
      IsRealLevyProcess Pboth (fun t omega => omega t) ∧
      IsRealLevyProcess Ppositive (fun t omega => omega t) ∧
      (∀ (t : NNReal) (theta : Real),
        (∫ omega : NNReal → Real,
          Complex.exp (Complex.I *
            (↑(theta * omega t) : Complex)) ∂Pboth) =
          Complex.exp (↑(-(t : Real) * (|theta| ^ alpha)) : Complex)) ∧
      (∀ (t : NNReal) (lambda : Real), 0 ≤ lambda →
        (∫ omega : NNReal → Real,
          Real.exp (-(lambda * omega t)) ∂Ppositive) =
          Real.exp (-(t : Real) * (lambda ^ alpha))) ∧
      IsRegularFor Pboth (fun t omega => omega t) 0 (Set.Ioi 0) ∧
      IsRegularFor Pboth (fun t omega => omega t) 0 (Set.Iio 0) ∧
      IsRegularFor Ppositive (fun t omega => omega t) 0 (Set.Ioi 0) ∧
      IsIrregularFor Ppositive (fun t omega => omega t) 0 (Set.Iio 0) ∧
      (∀ᵐ omega ∂Ppositive, ∀ t : NNReal, 0 ≤ omega t) ∧
      (∀ Q ∈ ({Pboth, Ppositive} : Set (Measure (NNReal → Real))),
        ∀ᵐ omega ∂Q, ∀ T : NNReal,
          ∃ C : Real, 0 ≤ C ∧
            ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
              StrictMono times → times (Fin.last n) ≤ T →
              (∑ i : Fin n,
                |omega (times i.succ) -
                  omega (times i.castSucc)|) ≤ C)

end Kyprianou.Ch06


