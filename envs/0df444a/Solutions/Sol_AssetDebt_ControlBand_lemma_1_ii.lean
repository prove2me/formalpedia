-- Prove2me | solution 1 for AssetDebt.ControlBand.lemma_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:15:58.106505+00:00
-- url     : https://prove2.me/submissions/5c7a63b1-9321-4af1-bba1-6d701646b27b

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

open MeasureTheory ProbabilityTheory AssetDebt.ControlBand

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ADCBG

lemma U_unfold (P : Params) (t : ℕ) (x p : ℝ) : U P t x p = if P.T < t then 0
    else sSup (objUStep P t x p (fun x' p' => U P (t + 1) x' p') '' Set.Icc 0 (min x P.ℓ)) := by
  rw [U]; rfl

lemma V_unfold (P : Params) (d : ℕ → ℝ) (m t : ℕ) (x w p : ℝ) : V P d m t x w p =
    if m < t then 0 else if p * min x P.ℓ + w < d t then 0
    else sSup (objV P d m t x w p '' {q | Feasible P d t x w p q}) := by
  rw [V]; rfl

/-- Discounted remaining debt `S_t = ∑_{i=t}^m ρ^{i-t} d_i`. -/
noncomputable def Sd (P : Params) (d : ℕ → ℝ) (m t : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc t m, P.ρ ^ (i - t) * d i

lemma Sd_m (P : Params) (d : ℕ → ℝ) (m : ℕ) : Sd P d m m = d m := by
  simp [Sd]

lemma Sd_succ (P : Params) (d : ℕ → ℝ) (m t : ℕ) (ht : t < m) :
    Sd P d m t = d t + P.ρ * Sd P d m (t + 1) := by
  unfold Sd
  rw [← Finset.insert_Icc_add_one_left_eq_Icc ht.le, Finset.sum_insert (by simp), Nat.sub_self,
    pow_zero, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [show i - t = (i - (t + 1)) + 1 by omega, pow_succ]; ring

lemma Sd_ge (P : Params) (hρ : 0 < P.ρ) (d : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i) (m t : ℕ) (ht : t ≤ m) :
    d t ≤ Sd P d m t := by
  rcases lt_or_eq_of_le ht with h | h
  · rw [Sd_succ P d m t h]
    have : 0 ≤ Sd P d m (t + 1) := Finset.sum_nonneg (fun i _ => mul_nonneg (pow_nonneg hρ.le _) (hd i))
    nlinarith
  · subst h; rw [Sd_m]

lemma U_zero (P : Params) (hℓ : 0 < P.ℓ) : ∀ k t, t + k = P.T + 1 → ∀ p, U P t 0 p = 0 := by
  intro k
  induction k with
  | zero => intro t ht p; rw [U_unfold, if_pos (by omega)]
  | succ k ih =>
    intro t ht p
    rw [U_unfold, if_neg (by omega), min_eq_left hℓ.le, Set.Icc_self, Set.image_singleton]
    unfold objUStep
    have : (fun p' => U P (t + 1) (0 - 0) p') = fun _ => 0 := by
      funext p'; rw [sub_self]; exact ih (t + 1) (by omega) p'
    rw [this]; simp

lemma U_zero' (P : Params) (hℓ : 0 < P.ℓ) (t : ℕ) (p : ℝ) : U P t 0 p = 0 := by
  by_cases h : P.T < t
  · rw [U_unfold, if_pos h]
  · exact U_zero P hℓ (P.T + 1 - t) t (by omega) p

lemma V_zero_x (P : Params) (hS : P.Standing) (d : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i) (m : ℕ) :
    ∀ k t, t + k = m → ∀ w p, 0 ≤ w → 0 < p → V P d m t 0 w p = max (w - Sd P d m t) 0 := by
  have hℓ : 0 < P.ℓ := hS.2.2.2.1
  have hρ : 0 < P.ρ := hS.2.1
  intro k
  induction k with
  | zero =>
    intro t ht w p hw hp
    have htm : t = m := by omega
    subst htm
    rw [V_unfold, if_neg (lt_irrefl _), min_eq_left hℓ.le, mul_zero, zero_add, Sd_m]
    by_cases hb : w < d t
    · rw [if_pos hb, max_eq_right (by linarith)]
    · rw [if_neg hb]
      have hset : {q | Feasible P d t 0 w p q} = {0} := by
        ext q; simp only [Feasible, Set.mem_setOf_eq, Set.mem_singleton_iff, min_eq_left hℓ.le]
        constructor
        · rintro ⟨a, b, _⟩; linarith
        · rintro rfl; refine ⟨le_rfl, le_rfl, by linarith⟩
      rw [hset, Set.image_singleton, csSup_singleton]
      unfold objV objVStep objU objUStep
      rw [if_pos rfl]
      simp only [mul_zero, sub_zero, zero_add]
      have : (fun p' => U P (t + 1) 0 p') = fun _ => 0 := funext (fun p' => U_zero' P hℓ _ _)
      rw [this]; simp only [integral_zero, mul_zero, zero_add]
      rw [max_eq_left (by linarith)]
  | succ k ih =>
    intro t ht w p hw hp
    have htm : t < m := by omega
    have := hS.2.2.2.2.2.1 t
    rw [V_unfold, if_neg (by omega), min_eq_left hℓ.le, mul_zero, zero_add]
    by_cases hb : w < d t
    · rw [if_pos hb, max_eq_right (by linarith [Sd_ge P hρ d hd m t htm.le])]
    · rw [if_neg hb]
      have hset : {q | Feasible P d t 0 w p q} = {0} := by
        ext q; simp only [Feasible, Set.mem_setOf_eq, Set.mem_singleton_iff, min_eq_left hℓ.le]
        constructor
        · rintro ⟨a, b, _⟩; linarith
        · rintro rfl; refine ⟨le_rfl, le_rfl, by linarith⟩
      rw [hset, Set.image_singleton, csSup_singleton]
      unfold objV objVStep
      rw [if_neg (by omega)]
      simp only [mul_zero, sub_zero, add_zero]
      have hae : (fun p' => V P d m (t + 1) 0 (P.ρ⁻¹ * (w - d t)) p') =ᵐ[P.κ t p]
          fun _ => max (P.ρ⁻¹ * (w - d t) - Sd P d m (t + 1)) 0 := by
        filter_upwards [hS.2.2.2.2.2.2.2.2 t p] with z hz
        exact ih (t + 1) (by omega) _ z (mul_nonneg (inv_nonneg.mpr hρ.le) (by linarith)) hz
      rw [integral_congr_ae hae, integral_const]
      simp only [probReal_univ, one_smul]
      rw [Sd_succ P d m t htm, mul_max_of_nonneg _ _ hρ.le, mul_zero]
      congr 1
      field_simp
      ring

end ADCBG

open ADCBG in
theorem solution (P : Params) (hS : P.Standing) (d : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (m : ℕ) (hm : 1 ≤ m ∧ m ≤ P.T) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ m)
    (w p : ℝ) (hw : 0 ≤ w) (hp : 0 < p) :
    V P d m t 0 w p = max (w - ∑ i ∈ Finset.Icc t m, P.ρ ^ (i - t) * d i) 0 :=
  V_zero_x P hS d hd m (m - t) t (by omega) w p hw hp
