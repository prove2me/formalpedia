-- Prove2me | Definitions.Def_Kyprianou_Ch06_BivariateSubordinator
-- name    : Kyprianou_Ch06_BivariateSubordinator
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:14:21.492743+00:00
-- url     : https://prove2.me/theorems/c3a8e468-0ab3-4f39-a77f-efc69ab229c3
-- title:
--   Joint bivariate chronological-height subordinator
-- statement:
--   A bivariate subordinator has joint stationary independent increments, nondecreasing nonnegative coordinates and càdlàg paths. The two coordinates are permitted to be dependent, as required by Theorem 6.10.
-- source:
--   Kyprianou (2006), §6.2, Theorem 6.10, printed p. 149.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Bivariate subordinator with stationary independent JOINT increments
and monotone cadlag sample paths. Spatial and chronological coordinates
need not be independent of one another. -/
def IsBivariateSubordinator
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (S : NNReal → Omega → NNReal × NNReal) : Prop :=
  (∀ t : NNReal, Measurable (S t)) ∧
  (∀ᵐ omega ∂P, S 0 omega = (0, 0)) ∧
  (∀ᵐ omega ∂P,
    Monotone (fun t : NNReal => (S t omega).1) ∧
    Monotone (fun t : NNReal => (S t omega).2)) ∧
  (∀ s t : NNReal,
    Measure.map (fun omega => S (s + t) omega - S s omega) P =
      Measure.map (S t) P) ∧
  (∀ (k : Nat) (times : Fin (k + 1) → NNReal),
    StrictMono times →
      ∀ A : Fin k → Set (NNReal × NNReal),
        (∀ i, MeasurableSet (A i)) →
        P {omega | ∀ i : Fin k,
          S (times i.succ) omega -
            S (times i.castSucc) omega ∈ A i} =
          ∏ i : Fin k,
            P {omega | S (times i.succ) omega -
              S (times i.castSucc) omega ∈ A i}) ∧
  (∀ᵐ omega ∂P, ∀ t : NNReal,
    ContinuousWithinAt (fun s : NNReal => S s omega)
      (Set.Ici t) t ∧
    (t = 0 ∨ ∃ x : NNReal × NNReal,
      Tendsto (fun s : NNReal => S s omega)
        (nhdsWithin t (Set.Iio t)) (nhds x)))

end Kyprianou.Ch06


