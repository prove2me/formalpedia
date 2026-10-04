-- Prove2me | solution 1 for Aumann1987.TwoPerson.devCond_iff_condPayoff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:43:16.789398+00:00
-- url     : https://prove2.me/submissions/528bca35-be1d-4c48-ae44-b4a97d572d75

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Real.Basic
import Definitions.Def_Aumann1987_TwoPerson_Model

open Finset

/-! Auxiliary lemma: split a finite sum at a single point. -/
lemma sum_split {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) (A : ℝ) (B : ι → ℝ) :
    ∑ x ∈ Finset.univ, (if x = j then A else B x) = A + ∑ x ∈ Finset.univ.erase j, B x := by
  classical
  rw [← Finset.add_sum_erase (s := Finset.univ) (f := fun x => if x = j then A else B x)
      (Finset.mem_univ j), if_pos rfl]
  congr 1
  exact Finset.sum_congr rfl fun x hx => by simp [Finset.ne_of_mem_erase hx]

open Aumann1987.TwoPerson in
theorem solution {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    (h₁ h₂ : S₁ → S₂ → ℝ) (p : S₁ → S₂ → ℝ) (hp : IsDistribution p) :
    (DevCond₁ h₁ p ↔
      ∀ j : S₁, 0 < ∑ k, p j k → ∀ q : S₁, condPayoff₁ h₁ p q j ≤ condPayoff₁ h₁ p j j) ∧
    (DevCond₂ h₂ p ↔
      ∀ k : S₂, 0 < ∑ j, p j k → ∀ r : S₂, condPayoff₂ h₂ p r k ≤ condPayoff₂ h₂ p k k) := by
  classical
  constructor
  · ---- player 1 ------------------------------------------------------------
    constructor
    · -- (2.2) ⇒ conditional-payoff form: test the single-point deviation
      intro hdev j hm q
      have key0 := hdev (fun x => if x = j then q else x)
      have hG : ∀ x ∈ Finset.univ,
          ∑ k, p x k * h₁ (if x = j then q else x) k
            = if x = j then ∑ k, p j k * h₁ q k else ∑ k, p x k * h₁ x k := by
        intro x _
        by_cases hx : x = j <;> simp [hx]
      have lhs : ∑ x, ∑ k, p x k * h₁ (if x = j then q else x) k
          = ∑ k, p j k * h₁ q k + (∑ x ∈ Finset.univ.erase j, ∑ k, p x k * h₁ x k) := by
        rw [Finset.sum_congr rfl hG, sum_split]
      have rhs : ∑ x, ∑ k, p x k * h₁ x k
          = ∑ k, p j k * h₁ j k + (∑ x ∈ Finset.univ.erase j, ∑ k, p x k * h₁ x k) := by
        rw [← Finset.add_sum_erase Finset.univ (fun x => ∑ k, p x k * h₁ x k)
          (Finset.mem_univ j)]
      have key : ∑ k, p j k * h₁ q k ≤ ∑ k, p j k * h₁ j k := by linarith
      have e1 : ∑ k, h₁ q k * p j k = ∑ k, p j k * h₁ q k :=
        Finset.sum_congr rfl fun k _ => mul_comm _ _
      have e2 : ∑ k, h₁ j k * p j k = ∑ k, p j k * h₁ j k :=
        Finset.sum_congr rfl fun k _ => mul_comm _ _
      have hdiv : (∑ k, h₁ q k * p j k) / (∑ k, p j k)
          ≤ (∑ k, h₁ j k * p j k) / (∑ k, p j k) := by
        refine (div_le_div_iff_of_pos_right (c := ∑ k, p j k) hm).mpr ?_
        rw [e1, e2]
        nlinarith [key]
      exact hdiv
    · -- conditional-payoff form ⇒ (2.2): weight the pointwise inequalities
      intro hcond φ
      have hpt : ∀ x ∈ Finset.univ,
          ∑ k, p x k * h₁ (φ x) k ≤ ∑ k, p x k * h₁ x k := by
        intro x _
        by_cases hx : 0 < ∑ k, p x k
        · have hdiv := hcond x hx (φ x)
          simp only [condPayoff₁] at hdiv
          have e1 : ∑ k, h₁ (φ x) k * p x k = ∑ k, p x k * h₁ (φ x) k :=
            Finset.sum_congr rfl fun k _ => mul_comm _ _
          have e2 : ∑ k, h₁ x k * p x k = ∑ k, p x k * h₁ x k :=
            Finset.sum_congr rfl fun k _ => mul_comm _ _
          rw [e1, e2] at hdiv
          have := (div_le_div_iff_of_pos_right (c := ∑ k, p x k) hx).mp hdiv
          exact this
        · -- null row: all weights vanish
          push_neg at hx
          have hz : ∑ k, p x k = 0 :=
            le_antisymm hx (Finset.sum_nonneg fun k _ => hp.1 x k)
          have hrow : ∀ k, p x k = 0 := fun k =>
            (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hp.1 x k)).mp hz k
              (Finset.mem_univ k)
          have e1 : ∑ k, p x k * h₁ (φ x) k = 0 :=
            Finset.sum_eq_zero fun k _ => by rw [hrow k]; ring
          have e2 : ∑ k, p x k * h₁ x k = 0 :=
            Finset.sum_eq_zero fun k _ => by rw [hrow k]; ring
          rw [e1, e2]
      exact Finset.sum_le_sum hpt
  · ---- player 2 ------------------------------------------------------------
    constructor
    · -- (2.2) ⇒ conditional-payoff form: test the single-point deviation
      intro hdev k hm r
      have key0 := hdev (fun y => if y = k then r else y)
      have h1' : (∑ j, ∑ y, p j y * h₂ j (if y = k then r else y))
          = ∑ y, ∑ j, p j y * h₂ j (if y = k then r else y) := Finset.sum_comm
      have h2' : (∑ j, ∑ y, p j y * h₂ j y)
          = ∑ y, ∑ j, p j y * h₂ j y := Finset.sum_comm
      rw [h1', h2'] at key0
      have hG : ∀ y ∈ Finset.univ,
          ∑ j, p j y * h₂ j (if y = k then r else y)
            = if y = k then ∑ j, p j k * h₂ j r else ∑ j, p j y * h₂ j y := by
        intro y _
        by_cases hy : y = k <;> simp [hy]
      have lhs : ∑ y, ∑ j, p j y * h₂ j (if y = k then r else y)
          = ∑ j, p j k * h₂ j r + (∑ y ∈ Finset.univ.erase k, ∑ j, p j y * h₂ j y) := by
        rw [Finset.sum_congr rfl hG, sum_split]
      have rhs : ∑ y, ∑ j, p j y * h₂ j y
          = ∑ j, p j k * h₂ j k + (∑ y ∈ Finset.univ.erase k, ∑ j, p j y * h₂ j y) := by
        rw [← Finset.add_sum_erase Finset.univ (fun y => ∑ j, p j y * h₂ j y)
          (Finset.mem_univ k)]
      have key : ∑ j, p j k * h₂ j r ≤ ∑ j, p j k * h₂ j k := by linarith
      have e1 : ∑ j, h₂ j r * p j k = ∑ j, p j k * h₂ j r :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      have e2 : ∑ j, h₂ j k * p j k = ∑ j, p j k * h₂ j k :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      have hdiv : (∑ j, h₂ j r * p j k) / (∑ j, p j k)
          ≤ (∑ j, h₂ j k * p j k) / (∑ j, p j k) := by
        refine (div_le_div_iff_of_pos_right (c := ∑ j, p j k) hm).mpr ?_
        rw [e1, e2]
        nlinarith [key]
      exact hdiv
    · -- conditional-payoff form ⇒ (2.2): weight the pointwise inequalities
      intro hcond ψ
      have hpt : ∀ y ∈ Finset.univ,
          ∑ j, p j y * h₂ j (ψ y) ≤ ∑ j, p j y * h₂ j y := by
        intro y _
        by_cases hy : 0 < ∑ j, p j y
        · have hdiv := hcond y hy (ψ y)
          simp only [condPayoff₂] at hdiv
          have e1 : ∑ j, h₂ j (ψ y) * p j y = ∑ j, p j y * h₂ j (ψ y) :=
            Finset.sum_congr rfl fun j _ => mul_comm _ _
          have e2 : ∑ j, h₂ j y * p j y = ∑ j, p j y * h₂ j y :=
            Finset.sum_congr rfl fun j _ => mul_comm _ _
          rw [e1, e2] at hdiv
          have := (div_le_div_iff_of_pos_right (c := ∑ j, p j y) hy).mp hdiv
          exact this
        · push_neg at hy
          have hz : ∑ j, p j y = 0 :=
            le_antisymm hy (Finset.sum_nonneg fun j _ => hp.1 j y)
          have hcol : ∀ j, p j y = 0 := fun j =>
            (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp.1 j y)).mp hz j
              (Finset.mem_univ j)
          have e1 : ∑ j, p j y * h₂ j (ψ y) = 0 :=
            Finset.sum_eq_zero fun j _ => by rw [hcol j]; ring
          have e2 : ∑ j, p j y * h₂ j y = 0 :=
            Finset.sum_eq_zero fun j _ => by rw [hcol j]; ring
          rw [e1, e2]
      calc ∑ j, ∑ k, p j k * h₂ j (ψ k)
          = ∑ k, ∑ j, p j k * h₂ j (ψ k) := Finset.sum_comm
        _ ≤ ∑ k, ∑ j, p j k * h₂ j k := Finset.sum_le_sum hpt
        _ = ∑ j, ∑ k, p j k * h₂ j k := Finset.sum_comm
