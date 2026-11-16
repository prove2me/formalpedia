-- Prove2me | Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
-- name    : Kyprianou_Ch05_RenewalEpochProcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:27:43.386803+00:00
-- url     : https://prove2.me/theorems/c0c92f74-e907-4caa-a86c-d80e84a08e90
-- title:
--   Independent renewal spacings, first-crossing epochs and joint renewal kernel
-- statement:
--   Renewal epochs T_0=0 and T_n as actual partial sums; nondegenerate nonnegative spacing law F, each new spacing independent of previous epoch with the correct common distribution; first strictly crossing epoch and exact overshoot/undershoot; measure-theoretic V(x-dy)F(y+du) kernel on measurable rectangles.
-- source:
--   Kyprianou (2006), Chapter 5, Lemma 5.5, pp.116-117.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- The nth renewal epoch is the sum of the first n spacings, T_0=0. -/
noncomputable def renewalEpoch
    {Omega : Type}
    (Z : Nat → Omega → Real) (n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n, Z k omega

/-- The spacings have common distribution F, nonnegative support, and each
new spacing is independent of the previous cumulative epoch. These
properties suffice for the renewal Markov/kernel identities and do not
assume the conclusions of Lemma 5.5. -/
def IsRenewalEpochProcess
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real) : Prop :=
  (∀ n : Nat, Measurable (Z n)) ∧
  (∀ n : Nat, Measure.map (Z n) P = F) ∧
  F (Set.Iio (0 : Real)) = 0 ∧
  F {0} ≠ 1 ∧
  ∀ (n : Nat) (A B : Set Real), MeasurableSet A → MeasurableSet B →
    P {omega : Omega |
      renewalEpoch Z n omega ∈ A ∧ Z n omega ∈ B} =
      P {omega : Omega | renewalEpoch Z n omega ∈ A} * F B

/-- First renewal epoch strictly above x, with fallback zero if absent. -/
noncomputable def nextRenewalIndex
    {Omega : Type}
    (Z : Nat → Omega → Real) (x : Real)
    (omega : Omega) : Nat :=
  sInf {n : Nat | 0 < n ∧ x < renewalEpoch Z n omega}

/-- Strictly positive overshoot at the first renewal after x. -/
noncomputable def renewalOvershoot
    {Omega : Type}
    (Z : Nat → Omega → Real) (x : Real)
    (omega : Omega) : Real :=
  renewalEpoch Z (nextRenewalIndex Z x omega) omega - x

/-- Undershoot to the last renewal at or below x. -/
noncomputable def renewalUndershoot
    {Omega : Type}
    (Z : Nat → Omega → Real) (x : Real)
    (omega : Omega) : Real :=
  x - renewalEpoch Z (nextRenewalIndex Z x omega - 1) omega

/-- The full renewal-kernel expression V(x-dy)F(y+du) on positive
overshoot and undershoot rectangles. -/
noncomputable def renewalJointKernel
    (V F : Measure Real) (x : Real)
    (A B : Set Real) : ENNReal := by
  classical
  exact ∫⁻ v in Set.Icc (0 : Real) x,
    (∫⁻ z in Set.Ioi (x-v),
      (if z-(x-v) ∈ A ∧ x-v ∈ B then
        (1 : ENNReal)
       else 0) ∂F) ∂V

end Kyprianou.Ch05


