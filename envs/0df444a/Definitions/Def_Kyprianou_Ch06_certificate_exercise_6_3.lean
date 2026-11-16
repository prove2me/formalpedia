-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_3
-- name    : Kyprianou_Ch06_certificate_exercise_6_3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:25:14.508208+00:00
-- url     : https://prove2.me/theorems/973b28b4-5a4f-494c-b2b5-f29c6f3c9df1
-- title:
--   Full quantified certificate for exercise:6.3
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Exercise 6.3, printed p. 175; two-up PDF p. 93.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from exponentialAndGeometricKillingOfCompoundPoissonAgree. -/
def certificate_exercise_6_3 : Prop :=
  ∀ (rho lambda : Real)
    (hRho : 0 < rho ∧ rho ≤ 1)
    (hLambda : 0 < lambda)
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Nslow Nfast : NNReal → Omega → Nat)
    (Yslow Yfast : Nat → Omega → NNReal)
    (killTime : Omega → WithTop NNReal)
    (geometricCount : Omega → WithTop Nat)
    (hSlow : ∀ t : NNReal, ∀ n : Nat,
      P {omega | Nslow t omega = n} =
        ProbabilityTheory.poissonMeasure
          (ENNReal.ofReal (lambda * rho * (t : Real))).toNNReal {n})
    (hFast : ∀ t : NNReal, ∀ n : Nat,
      P {omega | Nfast t omega = n} =
        ProbabilityTheory.poissonMeasure
          (ENNReal.ofReal (lambda * (t : Real))).toNNReal {n})
    (hKill : ∀ t : NNReal,
      P {omega | (t : WithTop NNReal) < killTime omega} =
        ENNReal.ofReal (Real.exp (-(lambda * (1-rho)) * (t : Real))))
    (hGeom : ∀ n : Nat,
      P {omega | geometricCount omega = (n : WithTop Nat)} =
        ENNReal.ofReal ((1-rho) * rho ^ n))
    (hGeomInfinity :
      P {omega | geometricCount omega = ⊤} =
        if rho = 1 then 1 else 0)
    (hMarkLaw : ∀ k : Nat, ∀ A : Fin k → Set NNReal,
      (∀ i, MeasurableSet (A i)) →
      P {omega | ∀ i : Fin k, Yslow i omega ∈ A i} =
        P {omega | ∀ i : Fin k, Yfast i omega ∈ A i})
    (hSlowCountIncrements : ∀ (k : Nat)
      (times : Fin (k + 1) → NNReal) (counts : Fin k → Nat),
      StrictMono times →
      P {omega | ∀ i : Fin k,
        Nslow (times i.succ) omega -
          Nslow (times i.castSucc) omega = counts i} =
        ∏ i : Fin k,
          ProbabilityTheory.poissonMeasure
            (ENNReal.ofReal (lambda * rho *
              (((times i.succ - times i.castSucc) : NNReal) : Real))).toNNReal
              {counts i})
    (hFastCountIncrements : ∀ (k : Nat)
      (times : Fin (k + 1) → NNReal) (counts : Fin k → Nat),
      StrictMono times →
      P {omega | ∀ i : Fin k,
        Nfast (times i.succ) omega -
          Nfast (times i.castSucc) omega = counts i} =
        ∏ i : Fin k,
          ProbabilityTheory.poissonMeasure
            (ENNReal.ofReal (lambda *
              (((times i.succ - times i.castSucc) : NNReal) : Real))).toNNReal
              {counts i})
    (hSlowIndependence : ∀ (m k : Nat)
      (times : Fin m → NNReal) (counts : Fin m → Nat)
      (u : NNReal) (A : Fin k → Set NNReal),
      (∀ i, MeasurableSet (A i)) →
      P {omega | (∀ j : Fin m,
          Nslow (times j) omega = counts j) ∧
        (u : WithTop NNReal) < killTime omega ∧
        (∀ i : Fin k, Yslow i omega ∈ A i)} =
        P {omega | ∀ j : Fin m,
          Nslow (times j) omega = counts j} *
        P {omega | (u : WithTop NNReal) < killTime omega} *
        P {omega | ∀ i : Fin k, Yslow i omega ∈ A i})
    (hFastIndependence : ∀ (m k : Nat)
      (times : Fin m → NNReal) (counts : Fin m → Nat)
      (z : WithTop Nat) (A : Fin k → Set NNReal),
      (∀ i, MeasurableSet (A i)) →
      P {omega | (∀ j : Fin m,
          Nfast (times j) omega = counts j) ∧
        geometricCount omega = z ∧
        (∀ i : Fin k, Yfast i omega ∈ A i)} =
        P {omega | ∀ j : Fin m,
          Nfast (times j) omega = counts j} *
        P {omega | geometricCount omega = z} *
        P {omega | ∀ i : Fin k, Yfast i omega ∈ A i}),
    ∀ (m : Nat) (times : Fin m → NNReal)
      (A : Fin m → Set (Option NNReal)),
      (∀ i, MeasurableSet (A i)) →
      P {omega | ∀ i : Fin m,
        (if (times i : WithTop NNReal) < killTime omega then
          some (∑ j ∈ Finset.range (Nslow (times i) omega),
            Yslow j omega) else none) ∈ A i} =
      P {omega | ∀ i : Fin m,
        (if (Nfast (times i) omega : WithTop Nat) ≤ geometricCount omega then
          some (∑ j ∈ Finset.range (Nfast (times i) omega),
            Yfast j omega) else none) ∈ A i}

end Kyprianou.Ch06


