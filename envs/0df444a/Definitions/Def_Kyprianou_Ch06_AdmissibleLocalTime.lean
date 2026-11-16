-- Prove2me | Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
-- name    : Kyprianou_Ch06_AdmissibleLocalTime
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:02:35.835685+00:00
-- url     : https://prove2.me/theorems/1826c34a-6c7a-435b-a3ca-4c1be2179132
-- title:
--   Chapter 6 admissible right-continuous local-time clocks
-- statement:
--   Extends the full support, adaptedness and stopping-time regeneration properties of Definition 6.1 to a right-continuous increasing local-time clock. This covers the discontinuous exponential-increment clock used when zero is irregular for the closed positive half-line. The filtration is explicitly right-continuous, as required for Lemma 6.9. In the regular half-line regime the local-time path must be continuous with zero origin. In the irregular regime it must be exactly the count of discrete maximum contacts marked by independent exponential variables, independent of the underlying Lévy process in all finite-dimensional cylinder laws. This excludes arbitrary independent random time changes.
-- source:
--   Kyprianou (2006), first edition, Theorem 6.7(ii), formula (6.5), Lemma 6.9 and standing filtration convention, printed pp. 144–149.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_ContinuousLocalTimeAtMaximum
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
open MeasureTheory Filter
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Usual right continuity of the filtration, F_t = intersect_{u>t} F_u. -/
def IsRightContinuousFiltration
    {Omega : Type} (F : NNReal → MeasurableSpace Omega) : Prop :=
  ∀ t : NNReal,
    F t = ⨅ u : {u : NNReal // t < u}, F u.1

/-- The discrete-clock alternative of (6.5): each maximum contact
receives one independent exponential mark, including the initial mark e_0.
Independence is required for all finite-dimensional path cylinders of X;
the distribution and count law jointly prevent arbitrary subordinator
time changes of a legitimate local-time clock. -/
def IsIndependentlyMarkedMaximumClock
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal) : Prop :=
  ∃ lambda : Real, 0 < lambda ∧
    ∃ marks : Nat → Omega → NNReal,
      (∀ i : Nat, Measurable (marks i)) ∧
      (∀ (i : Nat) (t : NNReal),
        P {omega | t < marks i omega} =
          ENNReal.ofReal (Real.exp (-lambda * (t : Real)))) ∧
      (∀ (k : Nat) (A : Fin k → Set NNReal),
        (∀ i, MeasurableSet (A i)) →
          P {omega | ∀ i : Fin k, marks i omega ∈ A i} =
            ∏ i : Fin k, P {omega | marks i omega ∈ A i}) ∧
      (∀ (k m : Nat) (A : Fin k → Set NNReal)
        (B : Fin m → Set Real) (times : Fin m → NNReal),
        (∀ i, MeasurableSet (A i)) →
        (∀ j, MeasurableSet (B j)) →
          P {omega | (∀ i : Fin k, marks i omega ∈ A i) ∧
            (∀ j : Fin m, X (times j) omega ∈ B j)} =
            P {omega | ∀ i : Fin k, marks i omega ∈ A i} *
            P {omega | ∀ j : Fin m, X (times j) omega ∈ B j}) ∧
      (∀ᵐ omega ∂P, ∀ t : NNReal,
        ∃ h : Set.Finite {u : NNReal | 0 < u ∧ u ≤ t ∧
            X u omega = runningMaximum X u omega},
          L t omega =
            ∑ i ∈ Finset.range (h.toFinset.card + 1),
              marks i omega)

/-- Admissible right-continuous local time, including the exponential-mark
jump clock of (6.5), which may start at a positive independent mark.
Its regeneration law compares the anchored clock L_t-L_0 against
increments L_(T+t)-L_T, avoiding a spurious contradiction at T=0.
The Stieltjes support condition handles jump atoms at right endpoints. -/
def IsAdmissibleLocalTimeAtMaximum
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal) : Prop :=
  IsFiltration F ∧
  IsRightContinuousFiltration F ∧
  (∀ t : NNReal,
    @Measurable Omega NNReal (F t) inferInstance (L t)) ∧
  (∀ᵐ omega ∂P,
     (∀ t : NNReal,
        ContinuousWithinAt (fun u : NNReal => L u omega) (Set.Ici t) t) ∧
     Monotone (fun t : NNReal => L t omega) ∧
     HasLocalTimeSupportAtMaximum X L omega) ∧
  (∃ t : NNReal, 0 < P {omega | L t omega ≠ 0}) ∧
  LocalTimeRegeneration P F X L ∧
  (IsRegularFor P X 0 (Set.Ici 0) →
    ∀ᵐ omega ∂P,
      Continuous (fun t : NNReal => L t omega) ∧
      L 0 omega = 0) ∧
  (IsIrregularFor P X 0 (Set.Ici 0) →
    IsIndependentlyMarkedMaximumClock P X L)

end Kyprianou.Ch06


