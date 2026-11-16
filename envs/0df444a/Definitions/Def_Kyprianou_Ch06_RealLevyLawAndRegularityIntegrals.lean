-- Prove2me | Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
-- name    : Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:04:02.181544+00:00
-- url     : https://prove2.me/theorems/e130b14e-734b-43b5-bcd8-dd98ac336d39
-- title:
--   Lévy path laws, compound Poisson class and Spitzer integrals
-- statement:
--   A real Lévy process has measurable marginals, zero initial state, finite-dimensional independent stationary increments and càdlàg paths. A compound Poisson process is a Poisson-counted jump sum with iid marks and no linear drift. The two nonnegative occupation-time logarithmic integrals are the quantities in Theorem 6.5 and Exercise 6.8. The identically zero process is explicitly a degenerate compound Poisson law (zero effective jump intensity), independently of whether the underlying probability space supports an auxiliary nontrivial Poisson count. This makes the non-compound-Poisson guard robust for the Chapter 6 factor-uniqueness theorem.
-- source:
--   Kyprianou (2006), Chapters 2 and 6; Theorem 6.5 p. 142 and Exercises 6.8 pp. 176–177.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- A real process has the finite-dimensional independent stationary increments,
zero initial state, measurable marginals and almost-sure cadlag paths of a
real-valued Levy process. The finite-dimensional independence clause includes
all disjoint ordered increment intervals, not merely pairwise independence. -/
def IsRealLevyProcess
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  (∀ t : NNReal, Measurable (X t)) ∧
  (∀ᵐ omega ∂P, X 0 omega = 0) ∧
  (∀ s t : NNReal,
    Measure.map (fun omega => X (s + t) omega - X s omega) P =
      Measure.map (X t) P) ∧
  (∀ (n : Nat) (times : Fin (n + 1) → NNReal),
    StrictMono times →
      ∀ A : Fin n → Set Real, (∀ i, MeasurableSet (A i)) →
      P {omega | ∀ i : Fin n,
          X (times i.succ) omega - X (times i.castSucc) omega ∈ A i} =
        ∏ i : Fin n,
          P {omega |
             X (times i.succ) omega - X (times i.castSucc) omega ∈ A i}) ∧
  (∀ᵐ omega ∂P, ∀ t : NNReal,
    ContinuousWithinAt (fun u : NNReal => X u omega) (Set.Ici t) t ∧
    (t = 0 ∨ ∃ x : Real,
      Tendsto (fun u : NNReal => X u omega)
        (nhdsWithin t (Set.Iio t)) (nhds x)))

/-- A compound Poisson process with zero linear drift: a Poisson event count
and a sequence of independent, identically distributed marks whose
running sum is the process, in equality of finite-dimensional laws.
The existence and iid laws of marks are part of the definition. -/
def IsCompoundPoissonProcess
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  (∀ᵐ omega ∂P, ∀ t : NNReal, X t omega = 0) ∨
  ∃ (rate : NNReal) (N : NNReal → Omega → Nat)
    (Y : Nat → Omega → Real),
    0 < rate ∧
    (∀ t : NNReal, Measurable (N t)) ∧
    (∀ i : Nat, Measurable (Y i)) ∧
    (∀ t : NNReal, ∀ n : Nat,
      P {omega | N t omega = n} =
        ProbabilityTheory.poissonMeasure (rate * t) {n}) ∧
    (∀ᵐ omega ∂P, ∀ t : NNReal,
      X t omega = ∑ i ∈ Finset.range (N t omega), Y i omega) ∧
    (∀ i j : Nat,
      Measure.map (Y i) P = Measure.map (Y j) P) ∧
    (∀ n : Nat, ∀ A : Fin n → Set Real,
      (∀ i, MeasurableSet (A i)) →
      P {omega | ∀ i : Fin n, Y i omega ∈ A i} =
        ∏ i : Fin n, P {omega | Y i omega ∈ A i}) ∧
    (∀ s t : NNReal, ∀ n : Nat,
      P {omega | N (s + t) omega - N s omega = n} =
        ProbabilityTheory.poissonMeasure (rate * t) {n}) ∧
    (∀ (k : Nat) (times : Fin (k + 1) → NNReal),
      StrictMono times →
      ∀ counts : Fin k → Set Nat, (∀ i, MeasurableSet (counts i)) →
        P {omega | ∀ i : Fin k,
          N (times i.succ) omega - N (times i.castSucc) omega ∈ counts i} =
          ∏ i : Fin k, P {omega |
            N (times i.succ) omega - N (times i.castSucc) omega ∈ counts i}) ∧
    (∀ (k m : Nat) (times : Fin k → NNReal)
      (counts : Fin k → Nat) (A : Fin m → Set Real),
      (∀ i, MeasurableSet (A i)) →
      P {omega | (∀ j : Fin k, N (times j) omega = counts j) ∧
        (∀ i : Fin m, Y i omega ∈ A i)} =
          P {omega | ∀ j : Fin k, N (times j) omega = counts j} *
          P {omega | ∀ i : Fin m, Y i omega ∈ A i})

/-- The positive-time upward-occupancy integrand in Theorem 6.5 and
Exercise 6.8. We integrate over real time and convert positive times
to the nonnegative time index of the process. -/
noncomputable def PositiveOccupationDiverges
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  (∫⁻ t in Set.Ioo (0 : Real) 1,
    ENNReal.ofReal (1 / t) *
      P {omega | X t.toNNReal omega > 0} ∂volume) = ⊤

/-- Closed half-line version of the Spitzer-Bertoin regularity test. -/
noncomputable def NonnegativeOccupationDiverges
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  (∫⁻ t in Set.Ioo (0 : Real) 1,
    ENNReal.ofReal (1 / t) *
      P {omega | 0 ≤ X t.toNNReal omega} ∂volume) = ⊤

/-- Subordinators are Levy processes with almost surely monotone sample paths. -/
def IsSubordinatorProcess
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  IsRealLevyProcess P X ∧
    (∀ᵐ omega ∂P, Monotone (fun t : NNReal => X t omega))

end Kyprianou.Ch06


