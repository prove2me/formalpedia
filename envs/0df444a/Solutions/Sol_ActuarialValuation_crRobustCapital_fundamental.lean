-- Prove2me | solution 1 for ActuarialValuation.crRobustCapital_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:16:42.076471+00:00
-- url     : https://prove2.me/submissions/f596d4e6-8aff-4f21-b1de-86baf86abeca

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crExpected
import Definitions.Def_actuarial_crPortfolioLoss
import Definitions.Def_actuarial_crMixWeights

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X Y : Fin n→ℝ) (c k mix : ℝ) (hp : ∀ i,0≤p i) (hq : ∀ i,0≤q i) (hpn : (∑ i : Fin n,p i)=1) (hqn : (∑ i : Fin n,q i)=1) (hXY : ∀ i,X i≤Y i) (hc : 0≤c) (hl0 : 0≤mix) (hl1 : mix≤1) : (crScenarioRisk p q X≤crScenarioRisk p q Y) ∧ (crScenarioRisk p q (fun i=>X i+k)=crScenarioRisk p q X+k) ∧ (crScenarioRisk p q (fun i=>c*X i)=c*crScenarioRisk p q X) ∧ (crScenarioRisk p q (crPortfolioLoss X Y)≤crScenarioRisk p q X+crScenarioRisk p q Y) ∧ (crExpected (crMixWeights p q mix) X≤crScenarioRisk p q X) := by
  have hadd (r A B : Fin n → ℝ) :
      crExpected r (fun i => A i + B i) = crExpected r A + crExpected r B := by
    unfold crExpected
    simp only [mul_add, Finset.sum_add_distrib]
  have hscale (r A : Fin n → ℝ) :
      crExpected r (fun i => c * A i) = c * crExpected r A := by
    unfold crExpected
    calc
      (∑ i : Fin n, r i * (c * A i)) = ∑ i : Fin n, c * (r i * A i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c * ∑ i : Fin n, r i * A i := by rw [Finset.mul_sum]
  have hconst (r : Fin n → ℝ) (hr : (∑ i : Fin n, r i) = 1) :
      crExpected r (fun _ => k) = k := by
    unfold crExpected
    calc
      (∑ i : Fin n, r i * k) = (∑ i : Fin n, r i) * k := by rw [Finset.sum_mul]
      _ = k := by rw [hr]; ring
  have hmono (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) :
      crExpected r X ≤ crExpected r Y := by
    unfold crExpected
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hXY i) (hr i)
  have hmix :
      crExpected (crMixWeights p q mix) X =
          mix * crExpected p X + (1-mix) * crExpected q X := by
    unfold crExpected crMixWeights
    calc
      (∑ i : Fin n, (mix * p i + (1-mix) * q i) * X i) =
        (∑ i : Fin n, mix * (p i * X i)) +
        (∑ i : Fin n, (1-mix) * (q i * X i)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
      _ = mix * (∑ i : Fin n, p i * X i) +
            (1-mix) * (∑ i : Fin n, q i * X i) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold crScenarioRisk
    apply max_le
    · exact (hmono p hp).trans (le_max_left _ _)
    · exact (hmono q hq).trans (le_max_right _ _)
  · have he1 := hadd p X (fun _ => k)
    have he2 := hadd q X (fun _ => k)
    rw [hconst p hpn] at he1
    rw [hconst q hqn] at he2
    unfold crScenarioRisk
    rw [he1, he2]
    rcases le_total (crExpected p X) (crExpected q X) with h | h
    · rw [max_eq_right h]
      apply max_eq_right
      linarith
    · rw [max_eq_left h]
      apply max_eq_left
      linarith
  · have h1 := hscale p X
    have h2 := hscale q X
    unfold crScenarioRisk
    rw [h1, h2]
    rcases le_total (crExpected p X) (crExpected q X) with h | h
    · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h hc)]
    · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h hc)]
  · change crScenarioRisk p q (fun i => X i + Y i) ≤
        crScenarioRisk p q X + crScenarioRisk p q Y
    unfold crScenarioRisk
    rw [hadd p X Y, hadd q X Y]
    apply max_le
    · have h1 := le_max_left (crExpected p X) (crExpected q X)
      have h2 := le_max_left (crExpected p Y) (crExpected q Y)
      linarith
    · have h1 := le_max_right (crExpected p X) (crExpected q X)
      have h2 := le_max_right (crExpected p Y) (crExpected q Y)
      linarith
  · rw [hmix]
    unfold crScenarioRisk
    have h1 := mul_le_mul_of_nonneg_left
      (le_max_left (crExpected p X) (crExpected q X)) hl0
    have h2 := mul_le_mul_of_nonneg_left
      (le_max_right (crExpected p X) (crExpected q X)) (sub_nonneg.mpr hl1)
    linarith
