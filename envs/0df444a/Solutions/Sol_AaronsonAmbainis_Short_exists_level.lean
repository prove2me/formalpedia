-- Prove2me | solution 1 for AaronsonAmbainis.Short.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:27:23.996613+00:00
-- url     : https://prove2.me/submissions/f0b56d03-5932-4d3c-a4a6-4775c40d075f

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Rows
open AaronsonAmbainis
open Finset

namespace AASolLevel

open MeasureTheory

theorem key (u v t : ℝ) :
    (decide (t < v) ≠ decide (t < u)) ↔ t ∈ Set.Ico (min u v) (max u v) := by
  rw [Set.mem_Ico, min_le_iff, lt_max_iff, ← not_lt, ← not_lt]
  simp only [ne_eq, decide_eq_decide]
  tauto

/-- The step function `t ↦ ∑ j, infl (lev f t) j` written as a sum of indicators. -/
noncomputable def G {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (t : ℝ) : ℝ :=
  ∑ j : ι, ∑ x : Cube ι,
    (Set.Ico (min (f x) (f (flipSet x {j}))) (max (f x) (f (flipSet x {j})))).indicator
      (fun _ => (1 : ℝ) / 2 ^ Fintype.card ι) t

theorem phi_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (t : ℝ) :
    ∑ j, infl (Level.lev f t) j = G f t := by
  unfold G
  apply Finset.sum_congr rfl
  intro j _
  unfold infl
  rw [Finset.natCast_card_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Set.indicator_apply]
  have hk : Level.lev f t (flipSet x {j}) ≠ Level.lev f t x ↔
      t ∈ Set.Ico (min (f x) (f (flipSet x {j}))) (max (f x) (f (flipSet x {j}))) :=
    key _ _ _
  by_cases h : t ∈ Set.Ico (min (f x) (f (flipSet x {j}))) (max (f x) (f (flipSet x {j})))
  · rw [if_pos h, if_pos (hk.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hk.1 h')), zero_div]

theorem term_integrable (a b c u v : ℝ) :
    IntegrableOn ((Set.Ico u v).indicator (fun _ => c)) (Set.Ioc a b) volume :=
  (integrableOn_const (by simp)).indicator measurableSet_Ico

theorem term_bound (a b c u v : ℝ) (hc : 0 ≤ c) :
    ∫ t in Set.Ioc a b, (Set.Ico (min u v) (max u v)).indicator (fun _ => c) t
      ≤ |u - v| * c := by
  rw [setIntegral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hc
  have h1 : volume.real (Set.Ioc a b ∩ Set.Ico (min u v) (max u v))
      ≤ volume.real (Set.Ico (min u v) (max u v)) :=
    measureReal_mono Set.inter_subset_right (by simp)
  have h2 : volume.real (Set.Ico (min u v) (max u v)) = |u - v| := by
    rw [Real.volume_real_Ico_of_le min_le_max, max_sub_min_eq_abs']
  linarith

theorem integral_G {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (a b : ℝ) :
    ∫ t in Set.Ioc a b, G f t ≤ ∑ j, meanAbsIncr f j := by
  unfold G
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun x _ => term_integrable _ _ _ _ _))]
  apply Finset.sum_le_sum
  intro j _
  rw [integral_finsetSum _ (fun x _ => term_integrable _ _ _ _ _)]
  unfold meanAbsIncr
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro x _
  have := term_bound a b ((1 : ℝ) / 2 ^ Fintype.card ι) (f x) (f (flipSet x {j})) (by positivity)
  rw [mul_one_div] at this
  exact this

theorem integrable_G {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (a b : ℝ) :
    IntegrableOn (G f) (Set.Ioc a b) volume := by
  unfold G
  exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun x _ => term_integrable _ _ _ _ _))

end AASolLevel

open AASolLevel MeasureTheory in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Cube ι → ℝ) (a b : ℝ) (hab : a < b) :
    ∃ t, a ≤ t ∧ t ≤ b ∧
      (b - a) * ∑ j, infl (Level.lev f t) j ≤ ∑ j, meanAbsIncr f j := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hμ : volume (Set.Ioc a b) ≠ 0 := by
    rw [Real.volume_Ioc]; simpa using hab
  obtain ⟨t, ht, hle⟩ := exists_le_setAverage hμ (by simp) (integrable_G f a b)
  refine ⟨t, ht.1.le, ht.2, ?_⟩
  rw [setAverage_eq, Real.volume_real_Ioc_of_le hab.le, smul_eq_mul] at hle
  rw [phi_eq]
  calc (b - a) * G f t ≤ (b - a) * ((b - a)⁻¹ * ∫ t in Set.Ioc a b, G f t) :=
        mul_le_mul_of_nonneg_left hle hba.le
    _ = ∫ t in Set.Ioc a b, G f t := by field_simp
    _ ≤ _ := integral_G f a b
