-- Prove2me | solution 1 for AffineStorage.Ruin.ruin_term_transform
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:16:51.024195+00:00
-- url     : https://prove2.me/submissions/3cb11f8b-74ad-4fc0-88cf-bea0f37a6f1e

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology
open AffineStorage.Ruin

lemma affRuinR_d_integrable (P : Params) (hS : P.Standing) :
    IntegrableOn P.d (Set.Ioi 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h1⟩ := hS
  by_contra h
  rw [integral_undef h] at h1
  norm_num at h1

/-- `e^{-sy} d(y)` is integrable on `(0,∞)` for `s ≥ 0`. -/
lemma affRuinR_lst_integrable (P : Params) (hS : P.Standing) (s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (fun y => Real.exp (-(s * y)) * P.d y) (Set.Ioi 0) := by
  have hdi := affRuinR_d_integrable P hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hdm, hd0, -, -⟩ := hS
  refine Integrable.mono' hdi
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).measurable.mul
      hdm).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hy' : (0 : ℝ) < y := hy
  have he : Real.exp (-(s * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hd0 y))]
  exact mul_le_of_le_one_left (hd0 y) he

/-- Fubini for the ruin term. -/
lemma affRuinR_fubini (P : Params) (hS : P.Standing) (ϑ : ℝ) (hϑ : 0 < ϑ) :
    (∫ x in Set.Ioi 0,
        (∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)))
          * (ϑ * Real.exp (-(ϑ * x))))
      = ∫ y in Set.Ioi 0, ∫ x in Set.Ioo 0 y,
          P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)) *
            (ϑ * Real.exp (-(ϑ * x))) := by
  have hdi := affRuinR_d_integrable P hS
  obtain ⟨-, -, -, -, -, -, -, hβ, hγ, hdm, hd0, -, -⟩ := hS
  set h : ℝ → ℝ → ℝ := fun x y => P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)) *
    (ϑ * Real.exp (-(ϑ * x))) with hh
  set f : ℝ → ℝ → ℝ := fun x y => (Set.Ioi x).indicator (h x) y with hf
  set μ := volume.restrict (Set.Ioi (0 : ℝ))
  have hwi : Integrable (fun x => ϑ * Real.exp (-(ϑ * x))) μ := by
    have := (exp_neg_integrableOn_Ioi 0 hϑ).const_mul ϑ
    simp only [neg_mul] at this; exact this
  have hint : Integrable (Function.uncurry f) (μ.prod μ) := by
    have hbound : Integrable (fun p : ℝ × ℝ => (ϑ * Real.exp (-(ϑ * p.1))) * P.d p.2)
        (μ.prod μ) := hwi.mul_prod hdi
    have hmeas : Measurable (Function.uncurry f) := by
      have heq : Function.uncurry f = {p : ℝ × ℝ | p.1 < p.2}.indicator
          (fun p => h p.1 p.2) := by
        funext p
        simp only [Function.uncurry, hf, Set.indicator, Set.mem_Ioi, Set.mem_setOf_eq]
      rw [heq]
      refine Measurable.indicator ?_ (measurableSet_lt measurable_fst measurable_snd)
      simp only [hh]
      exact (((hdm.comp measurable_snd).mul (by fun_prop)).mul (by fun_prop)).mul (by fun_prop)
    refine Integrable.mono' hbound hmeas.aestronglyMeasurable ?_
    simp only [μ]
    rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
    refine Filter.Eventually.of_forall fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : (0 : ℝ) < p.1 := hp1
    simp only [Function.uncurry, hf]
    by_cases hlt : p.1 < p.2
    · rw [Set.indicator_of_mem (show p.2 ∈ Set.Ioi p.1 from hlt)]
      simp only [hh]
      have e1 : Real.exp (-(P.β * (p.2 - p.1))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      have e2 : Real.exp (-(P.γ * p.1)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hw : 0 < ϑ * Real.exp (-(ϑ * p.1)) := mul_pos hϑ (Real.exp_pos _)
      have hnn : 0 ≤ P.d p.2 * Real.exp (-(P.β * (p.2 - p.1))) * Real.exp (-(P.γ * p.1)) :=
        mul_nonneg (mul_nonneg (hd0 _) (Real.exp_pos _).le) (Real.exp_pos _).le
      have hle : P.d p.2 * Real.exp (-(P.β * (p.2 - p.1))) * Real.exp (-(P.γ * p.1)) ≤ P.d p.2 := by
        rw [mul_assoc]
        exact mul_le_of_le_one_right (hd0 _)
          (by nlinarith [Real.exp_pos (-(P.β * (p.2 - p.1))), Real.exp_pos (-(P.γ * p.1))])
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn hw.le), mul_comm _ (P.d p.2)]
      exact mul_le_mul_of_nonneg_right hle hw.le
    · rw [Set.indicator_of_notMem (show p.2 ∉ Set.Ioi p.1 from hlt)]
      simp only [norm_zero]
      exact mul_nonneg (mul_pos hϑ (Real.exp_pos _)).le (hd0 _)
  have hswap := integral_integral_swap hint
  have hL : ∀ x, 0 < x → ∫ y, f x y ∂μ =
      (∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)))
          * (ϑ * Real.exp (-(ϑ * x))) := by
    intro x hx
    simp only [μ, hf]
    rw [setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hx.le), ← integral_mul_const]
  have hR : ∀ y, 0 < y → ∫ x, f x y ∂μ = ∫ x in Set.Ioo 0 y, h x y := by
    intro y hy
    have : ∀ x, f x y = (Set.Iio y).indicator (fun x => h x y) x := by
      intro x
      simp only [hf, Set.indicator, Set.mem_Ioi, Set.mem_Iio]
    simp only [μ, this]
    rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  calc (∫ x in Set.Ioi 0,
        (∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)))
          * (ϑ * Real.exp (-(ϑ * x))))
      = ∫ x, ∫ y, f x y ∂μ ∂μ :=
        (setIntegral_congr_fun measurableSet_Ioi fun x hx => (hL x hx).symm)
    _ = ∫ y, ∫ x, f x y ∂μ ∂μ := hswap
    _ = _ := setIntegral_congr_fun measurableSet_Ioi fun y hy => hR y hy

lemma affRuinR_inner (P : Params) (ϑ y : ℝ) (hy : 0 < y) :
    ∫ x in Set.Ioo 0 y, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)) *
        (ϑ * Real.exp (-(ϑ * x)))
      = P.d y * ϑ * Real.exp (-(P.β * y)) *
          ∫ x in (0:ℝ)..y, Real.exp ((P.β - P.γ - ϑ) * x) := by
  have e : ∀ x, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)) *
      (ϑ * Real.exp (-(ϑ * x))) = P.d y * ϑ * Real.exp (-(P.β * y)) *
        Real.exp ((P.β - P.γ - ϑ) * x) := by
    intro x
    have : Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)) * Real.exp (-(ϑ * x))
        = Real.exp (-(P.β * y)) * Real.exp ((P.β - P.γ - ϑ) * x) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    linear_combination (P.d y * ϑ) * this
  simp_rw [e]
  rw [integral_const_mul, intervalIntegral.integral_of_le hy.le, integral_Ioc_eq_integral_Ioo]

lemma affRuinR_expint (k y : ℝ) (hk : k ≠ 0) :
    ∫ x in (0:ℝ)..y, Real.exp (k * x) = (Real.exp (k * y) - 1) / k := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) y, HasDerivAt (fun x => Real.exp (k * x) / k)
      (Real.exp (k * x)) x := by
    intro x _
    have := ((hasDerivAt_id' x).const_mul k).exp.div_const k
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x => Real.exp (k * x)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.exp_zero]
  ring

theorem solution (P : Params) (hS : P.Standing) (ϑ : ℝ) (hϑ : 0 < ϑ) :
    (ϑ + P.γ ≠ P.β →
      P.lamMinus * (∫ x in Set.Ioi 0,
          (∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)))
            * (ϑ * Real.exp (-(ϑ * x))))
        = P.lamMinus * ϑ * (∫ y in Set.Ioi 0,
            (Real.exp (-(P.β * y)) - Real.exp (-((ϑ + P.γ) * y))) / (ϑ + P.γ - P.β) * P.d y) ∧
      P.lamMinus * ϑ * (∫ y in Set.Ioi 0,
            (Real.exp (-(P.β * y)) - Real.exp (-((ϑ + P.γ) * y))) / (ϑ + P.γ - P.β) * P.d y)
        = P.lamMinus * ϑ * ((P.lst P.β - P.lst (ϑ + P.γ)) / (ϑ + P.γ - P.β))) ∧
    P.lamMinus * (∫ x in Set.Ioi 0,
        (∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)))
          * (ϑ * Real.exp (-(ϑ * x))))
      = P.r * ϑ * G3 P ϑ := by
  have hr : 0 < P.r := hS.2.1
  have hβ : 0 ≤ P.β := hS.2.2.2.2.2.2.2.1
  have hγ : 0 ≤ P.γ := hS.2.2.2.2.2.2.2.2.1
  have hfub := affRuinR_fubini P hS ϑ hϑ
  -- the case `ϑ + γ ≠ β`
  have hA : ϑ + P.γ ≠ P.β →
      (∫ x in Set.Ioi 0,
          (∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)))
            * (ϑ * Real.exp (-(ϑ * x))))
        = ϑ * (∫ y in Set.Ioi 0,
            (Real.exp (-(P.β * y)) - Real.exp (-((ϑ + P.γ) * y))) / (ϑ + P.γ - P.β) * P.d y) := by
    intro hne
    have hk : P.β - P.γ - ϑ ≠ 0 := fun h => hne (by linarith)
    have hk' : ϑ + P.γ - P.β ≠ 0 := fun h => hne (by linarith)
    rw [hfub, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    rw [affRuinR_inner P ϑ y hy, affRuinR_expint _ _ hk]
    have he : Real.exp (-((ϑ + P.γ) * y)) = Real.exp (-(P.β * y)) * Real.exp ((P.β - P.γ - ϑ) * y) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    field_simp
    ring
  have hB : ϑ + P.γ ≠ P.β →
      P.lamMinus * ϑ * (∫ y in Set.Ioi 0,
            (Real.exp (-(P.β * y)) - Real.exp (-((ϑ + P.γ) * y))) / (ϑ + P.γ - P.β) * P.d y)
        = P.lamMinus * ϑ * ((P.lst P.β - P.lst (ϑ + P.γ)) / (ϑ + P.γ - P.β)) := by
    intro hne
    have i1 := affRuinR_lst_integrable P hS P.β hβ
    have i2 := affRuinR_lst_integrable P hS (ϑ + P.γ) (by linarith)
    congr 1
    unfold Params.lst
    rw [← integral_sub i1 i2, ← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    ring
  refine ⟨fun hne => ⟨by rw [hA hne]; ring, hB hne⟩, ?_⟩
  by_cases hne : ϑ + P.γ = P.β
  · -- removable singularity
    have hk0 : P.β - P.γ - ϑ = 0 := by linarith
    have hI : (∫ y in Set.Ioi 0, ∫ x in Set.Ioo 0 y,
          P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)) *
            (ϑ * Real.exp (-(ϑ * x))))
        = ϑ * ∫ y in Set.Ioi 0, y * Real.exp (-(P.β * y)) * P.d y := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      rw [affRuinR_inner P ϑ y hy, hk0]
      simp only [zero_mul, Real.exp_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
        mul_one]
      ring
    rw [hfub, hI]
    unfold G3
    rw [if_pos hne]
    generalize (∫ y in Set.Ioi 0, y * Real.exp (-(P.β * y)) * P.d y) = X
    field_simp
  · rw [hA hne, ← mul_assoc]
    have := hB hne
    unfold G3
    rw [if_neg hne]
    rw [show P.lamMinus * ϑ * ∫ y in Set.Ioi 0,
        (Real.exp (-(P.β * y)) - Real.exp (-((ϑ + P.γ) * y))) / (ϑ + P.γ - P.β) * P.d y
        = P.lamMinus * ϑ * ((P.lst P.β - P.lst (ϑ + P.γ)) / (ϑ + P.γ - P.β)) from this]
    field_simp
