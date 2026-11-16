-- Prove2me | Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
-- name    : Kyprianou_Ch06_MarkedPoissonPointProcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:11:27.106786+00:00
-- url     : https://prove2.me/theorems/295d2b6c-463e-47f1-bd3f-fef1cb193b66
-- title:
--   Time-marked Poisson point process: disjoint rectangle laws
-- statement:
--   A marked Poisson point process is a measurable, monotonically increasing marked counting process whose counts on any finite family of disjoint time-mark rectangles are independent Poisson variables with their product-intensity parameters. This includes both disjoint time intervals and disjoint mark categories, as required for Lemma 6.18.
-- source:
--   Kyprianou (2006), §6.3 and Lemma 6.18, printed pp. 155 and 160–161.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Rectangular finite-dimensional count laws for a time-homogeneous
Poisson point process of E-valued marks with sigma-finite intensity n.
The pairwise-disjoint time/mark rectangles have independent Poisson
counts; overlapping time intervals are allowed for disjoint marks. -/
def IsMarkedPoissonPointProcess
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat) : Prop :=
  (∀ (t : NNReal) (A : Set E), MeasurableSet A →
    Measurable (fun omega => N omega t A)) ∧
  (∀ᵐ omega ∂P,
    (∀ A : Set E, N omega 0 A = 0) ∧
    (∀ t : NNReal, ∀ A B : Set E,
      Disjoint A B →
        N omega t (A ∪ B) =
          N omega t A + N omega t B) ∧
    (∀ A : Set E, Monotone (fun t : NNReal => N omega t A))) ∧
  (∀ (k : Nat) (start stop : Fin k → NNReal)
     (A : Fin k → Set E) (counts : Fin k → Nat),
    (∀ i, start i ≤ stop i ∧
      MeasurableSet (A i) ∧ n (A i) < ⊤) →
    (∀ i j : Fin k, i ≠ j →
      stop i ≤ start j ∨ stop j ≤ start i ∨
        Disjoint (A i) (A j)) →
    P {omega | ∀ i : Fin k,
      N omega (stop i) (A i) -
        N omega (start i) (A i) = counts i} =
      ∏ i : Fin k,
        ProbabilityTheory.poissonMeasure
          ((stop i - start i) * (n (A i)).toNNReal)
          {counts i})

end Kyprianou.Ch06


