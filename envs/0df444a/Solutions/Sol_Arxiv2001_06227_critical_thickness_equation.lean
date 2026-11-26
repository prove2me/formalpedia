-- Prove2me | solution 1 for Arxiv2001_06227.critical_thickness_equation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:00:48.562273+00:00
-- url     : https://prove2.me/submissions/518837ce-c676-4742-b86d-3b698a205b61

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology Set

namespace S77CT
open Arxiv2001_06227

lemma hasDerivAt_mul_cont (K : ℝ → ℝ) (hK : ContinuousAt K 0) :
    HasDerivAt (fun x => x * K x) (K 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have : slope (fun x => x * K x) 0 =ᶠ[𝓝[≠] 0] K := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_def_field]; simp only [zero_mul, sub_zero]
    field_simp [show x ≠ 0 from hx]
  rw [tendsto_congr' this]
  exact hK.tendsto.mono_left nhdsWithin_le_nhds

noncomputable def F1 (p : ℝ → ℝ → ℝ) (muA L x μ : ℝ) : ℝ :=
  1 / (muA + x) * ((μ / (μ + 1)) * p (-μ) 1 * (1 - Real.exp (-((muA + x) * L * ((μ + 1) / μ)))))

noncomputable def F2 (p : ℝ → ℝ → ℝ) (muA L x μ : ℝ) : ℝ :=
  1 / (muA + x) * ((μ / (μ - 1)) * p μ 1 * (1 - Real.exp (-((muA + x) * L * ((μ - 1) / μ)))) *
    Real.exp (-((muA + x) * L / μ)))

lemma rt_eq (p : ℝ → ℝ → ℝ) (muA L x : ℝ) :
    slabRT p x muA L = Real.exp (-((muA + x) * L)) +
      x * (∫ μ in Ioo (0:ℝ) 1, F1 p muA L x μ) + x * (∫ μ in Ioo (0:ℝ) 1, F2 p muA L x μ) := by
  unfold slabRT F1 F2
  rw [← integral_const_mul, ← integral_const_mul]
  congr 2
  · congr 1; funext μ; ring
  · funext μ; ring

lemma bd2 (c L μ : ℝ) (hc : 0 < c) (hL : 0 < L) (hμ : μ ∈ Ioo (0:ℝ) 1) :
    0 ≤ μ / (μ - 1) * (1 - Real.exp (-(c * L * ((μ - 1) / μ)))) * Real.exp (-(c * L / μ)) ∧
    μ / (μ - 1) * (1 - Real.exp (-(c * L * ((μ - 1) / μ)))) * Real.exp (-(c * L / μ)) ≤ c * L := by
  obtain ⟨h0, h1⟩ := hμ
  set t := c * L * ((1 - μ) / μ) with ht
  have ht0 : 0 ≤ t := by positivity
  have hE : Real.exp (-(c * L * ((μ - 1) / μ))) * Real.exp (-(c * L / μ)) = Real.exp (-(c * L)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hE2 : Real.exp (-(c * L * ((μ - 1) / μ))) = Real.exp t := by
    congr 1; rw [ht]; field_simp; ring
  have hexpr : μ / (μ - 1) * (1 - Real.exp (-(c * L * ((μ - 1) / μ)))) * Real.exp (-(c * L / μ))
      = μ / (1 - μ) * (Real.exp (-(c * L)) * (1 - Real.exp (-t))) := by
    have hE3 : Real.exp (-(c * L)) * Real.exp (-t) = Real.exp (-(c * L / μ)) := by
      rw [← Real.exp_add]; congr 1; rw [ht]; field_simp; ring
    have hm : μ - 1 ≠ 0 := by linarith
    have hm' : 1 - μ ≠ 0 := by linarith
    rw [show μ / (μ - 1) = -(μ / (1 - μ)) by field_simp; ring]
    linear_combination (μ / (1 - μ)) * hE + (μ / (1 - μ)) * hE3
  rw [hexpr]
  have e1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have e2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have e3 : Real.exp (-(c * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have e4 : 0 < Real.exp (-(c * L)) := Real.exp_pos _
  have hq : 0 ≤ μ / (1 - μ) := div_nonneg h0.le (by linarith)
  refine ⟨mul_nonneg hq (mul_nonneg e4.le (by linarith)), ?_⟩
  have : μ / (1 - μ) * t = c * L := by rw [ht]; field_simp [show 1 - μ ≠ 0 by linarith]
  calc μ / (1 - μ) * (Real.exp (-(c * L)) * (1 - Real.exp (-t))) ≤ μ / (1 - μ) * (1 * t) := by
        apply mul_le_mul_of_nonneg_left _ hq
        exact mul_le_mul e3 (by linarith) (by linarith) zero_le_one
    _ = c * L := by rw [one_mul, this]

lemma bd1 (c L μ : ℝ) (hc : 0 < c) (hL : 0 < L) (hμ : μ ∈ Ioo (0:ℝ) 1) :
    0 ≤ μ / (μ + 1) * (1 - Real.exp (-(c * L * ((μ + 1) / μ)))) ∧
    μ / (μ + 1) * (1 - Real.exp (-(c * L * ((μ + 1) / μ)))) ≤ 1 := by
  obtain ⟨h0, h1⟩ := hμ
  have e : Real.exp (-(c * L * ((μ + 1) / μ))) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ c * L * ((μ + 1) / μ) := by positivity
    linarith)
  have e' := Real.exp_pos (-(c * L * ((μ + 1) / μ)))
  have q0 : 0 ≤ μ / (μ + 1) := by positivity
  have q1 : μ / (μ + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  exact ⟨mul_nonneg q0 (by linarith), by
    calc μ / (μ + 1) * (1 - Real.exp (-(c * L * ((μ + 1) / μ)))) ≤ 1 * 1 :=
          mul_le_mul q1 (by linarith) (by linarith) zero_le_one
      _ = 1 := by norm_num⟩


lemma hq_neg (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p) :
    IntegrableOn (fun μ => p (-μ) 1) (Ioo (0:ℝ) 1) := by
  have hI : IntervalIntegrable (fun μ => p μ 1) volume (-1) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2
      (hp.2.1.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by norm_num))))
  have := (IntervalIntegrable.iff_comp_neg).1 hI
  rw [neg_neg, neg_zero] at this
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 this.symm

lemma hq_pos (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p) :
    IntegrableOn (fun μ => p μ 1) (Ioo (0:ℝ) 1) :=
  hp.2.1.mono_set (Ioo_subset_Icc_self.trans (Icc_subset_Icc (by norm_num) le_rfl))

lemma F1_meas (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p) (muA L x : ℝ) :
    AEStronglyMeasurable (F1 p muA L x) (volume.restrict (Ioo (0:ℝ) 1)) := by
  unfold F1
  exact (((by fun_prop : Measurable fun μ : ℝ => μ / (μ + 1)).aestronglyMeasurable.mul
    (hq_neg p hp).aestronglyMeasurable).mul
    (by fun_prop : Measurable fun μ : ℝ =>
      (1 - Real.exp (-((muA + x) * L * ((μ + 1) / μ))))).aestronglyMeasurable).const_mul _

lemma F2_meas (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p) (muA L x : ℝ) :
    AEStronglyMeasurable (F2 p muA L x) (volume.restrict (Ioo (0:ℝ) 1)) := by
  unfold F2
  exact ((((by fun_prop : Measurable fun μ : ℝ => μ / (μ - 1)).aestronglyMeasurable.mul
    (hq_pos p hp).aestronglyMeasurable).mul
    (by fun_prop : Measurable fun μ : ℝ =>
      (1 - Real.exp (-((muA + x) * L * ((μ - 1) / μ))))).aestronglyMeasurable).mul
    (by fun_prop : Measurable fun μ : ℝ => Real.exp (-((muA + x) * L / μ))).aestronglyMeasurable).const_mul _

lemma F1_bd (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p) (muA L x μ : ℝ) (hmuA : 0 < muA)
    (hL : 0 < L) (hx : x ∈ Ioo (-(muA / 2)) (muA / 2)) (hμ : μ ∈ Ioo (0:ℝ) 1) :
    ‖F1 p muA L x μ‖ ≤ 2 / muA * p (-μ) 1 := by
  have hc : 0 < muA + x := by linarith [hx.1]
  have hc2 : 1 / (muA + x) ≤ 2 / muA := by
    rw [div_le_div_iff₀ hc hmuA]; linarith [hx.1]
  obtain ⟨b0, b1⟩ := bd1 (muA + x) L μ hc hL hμ
  have hp0 := hp.1 (-μ) 1
  have : F1 p muA L x μ = 1 / (muA + x) * p (-μ) 1 *
      (μ / (μ + 1) * (1 - Real.exp (-((muA + x) * L * ((μ + 1) / μ))))) := by
    unfold F1; ring
  rw [this, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc 1 / (muA + x) * p (-μ) 1 * (μ / (μ + 1) * (1 - Real.exp (-((muA + x) * L * ((μ + 1) / μ)))))
      ≤ 2 / muA * p (-μ) 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hc2 hp0) b1 b0 (by positivity)
    _ = 2 / muA * p (-μ) 1 := mul_one _

lemma F2_bd (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p) (muA L x μ : ℝ) (hmuA : 0 < muA)
    (hL : 0 < L) (hx : x ∈ Ioo (-(muA / 2)) (muA / 2)) (hμ : μ ∈ Ioo (0:ℝ) 1) :
    ‖F2 p muA L x μ‖ ≤ L * p μ 1 := by
  have hc : 0 < muA + x := by linarith [hx.1]
  obtain ⟨b0, b1⟩ := bd2 (muA + x) L μ hc hL hμ
  have hp0 := hp.1 μ 1
  have : F2 p muA L x μ = 1 / (muA + x) * p μ 1 *
      (μ / (μ - 1) * (1 - Real.exp (-((muA + x) * L * ((μ - 1) / μ)))) *
        Real.exp (-((muA + x) * L / μ))) := by
    unfold F2; ring
  rw [this, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc _ ≤ 1 / (muA + x) * p μ 1 * ((muA + x) * L) :=
        mul_le_mul_of_nonneg_left b1 (by positivity)
    _ = L * p μ 1 := by field_simp

lemma K1_cont (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p) (muA L : ℝ) (hmuA : 0 < muA)
    (hL : 0 < L) : ContinuousAt (fun x => ∫ μ in Ioo (0:ℝ) 1, F1 p muA L x μ) 0 := by
  apply continuousAt_of_dominated (bound := fun μ => 2 / muA * p (-μ) 1)
  · exact Eventually.of_forall (fun x => F1_meas p hp muA L x)
  · filter_upwards [Ioo_mem_nhds (by linarith : -(muA / 2) < 0) (by linarith : (0:ℝ) < muA / 2)]
      with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with μ hμ
    exact F1_bd p hp muA L x μ hmuA hL hx hμ
  · exact (hq_neg p hp).const_mul _
  · refine Eventually.of_forall (fun μ => ?_)
    unfold F1
    apply ContinuousAt.mul
    · exact continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simp; linarith)
    · exact (by fun_prop : Continuous fun x : ℝ => (μ / (μ + 1)) * p (-μ) 1 *
        (1 - Real.exp (-((muA + x) * L * ((μ + 1) / μ))))).continuousAt

lemma K2_cont (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p) (muA L : ℝ) (hmuA : 0 < muA)
    (hL : 0 < L) : ContinuousAt (fun x => ∫ μ in Ioo (0:ℝ) 1, F2 p muA L x μ) 0 := by
  apply continuousAt_of_dominated (bound := fun μ => L * p μ 1)
  · exact Eventually.of_forall (fun x => F2_meas p hp muA L x)
  · filter_upwards [Ioo_mem_nhds (by linarith : -(muA / 2) < 0) (by linarith : (0:ℝ) < muA / 2)]
      with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with μ hμ
    exact F2_bd p hp muA L x μ hmuA hL hx hμ
  · exact (hq_pos p hp).const_mul _
  · refine Eventually.of_forall (fun μ => ?_)
    unfold F2
    apply ContinuousAt.mul
    · exact continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simp; linarith)
    · exact (by fun_prop : Continuous fun x : ℝ => (μ / (μ - 1)) * p μ 1 *
        (1 - Real.exp (-((muA + x) * L * ((μ - 1) / μ)))) *
          Real.exp (-((muA + x) * L / μ))).continuousAt

end S77CT

open Arxiv2001_06227 S77CT in
theorem solution (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p)
    (P0 muA L : ℝ) (hP0 : 0 < P0) (hmuA : 0 < muA) (hL : 0 < L) :
    DifferentiableAt ℝ (fun muS => slabAbsorbed p P0 muS muA L) 0 ∧
    (deriv (fun muS => slabAbsorbed p P0 muS muA L) 0 = 0 ↔ criticalLHS p (muA * L) = 0) := by
  set K1 := fun x => ∫ μ in Ioo (0:ℝ) 1, F1 p muA L x μ with hK1
  set K2 := fun x => ∫ μ in Ioo (0:ℝ) 1, F2 p muA L x μ with hK2
  have hfun : (fun muS => slabAbsorbed p P0 muS muA L) =
      fun x => P0 * (1 - (Real.exp (-((muA + x) * L)) + x * K1 x + x * K2 x)) := by
    funext x; unfold slabAbsorbed; rw [rt_eq]
  have hE : HasDerivAt (fun x : ℝ => Real.exp (-((muA + x) * L)))
      (Real.exp (-((muA + 0) * L)) * (-(1 * L))) 0 :=
    (((hasDerivAt_id' (0:ℝ)).const_add muA).mul_const L).neg.exp
  have h1 := hasDerivAt_mul_cont K1 (K1_cont p hp muA L hmuA hL)
  have h2 := hasDerivAt_mul_cont K2 (K2_cont p hp muA L hmuA hL)
  have hd : HasDerivAt (fun x => P0 * (1 - (Real.exp (-((muA + x) * L)) + x * K1 x + x * K2 x)))
      (P0 * -(Real.exp (-((muA + 0) * L)) * -(1 * L) + K1 0 + K2 0)) 0 :=
    (((hE.add h1).add h2).const_sub 1).const_mul P0
  rw [hfun]
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  -- integrability at x = 0
  have hx0 : (0:ℝ) ∈ Ioo (-(muA / 2)) (muA / 2) := ⟨by linarith, by linarith⟩
  have i1 : Integrable (F1 p muA L 0) (volume.restrict (Ioo (0:ℝ) 1)) :=
    ((hq_neg p hp).const_mul (2 / muA)).mono' (F1_meas p hp muA L 0)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with μ hμ
          exact F1_bd p hp muA L 0 μ hmuA hL hx0 hμ)
  have i2 : Integrable (F2 p muA L 0) (volume.restrict (Ioo (0:ℝ) 1)) :=
    ((hq_pos p hp).const_mul L).mono' (F2_meas p hp muA L 0)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with μ hμ
          exact F2_bd p hp muA L 0 μ hmuA hL hx0 hμ)
  have hcrit : criticalLHS p (muA * L) = muA * K1 0 + muA * K2 0 -
      muA * L * Real.exp (-(muA * L)) := by
    unfold criticalLHS
    congr 1
    rw [hK1, hK2]
    simp only
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _) (i2.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioo (fun μ hμ => ?_)
    have hμ0 : μ ≠ 0 := hμ.1.ne'
    have hμ1 : μ - 1 ≠ 0 := by linarith [hμ.2]
    have hμ1' : 1 - μ ≠ 0 := by linarith [hμ.2]
    have hμ2 : μ + 1 ≠ 0 := by linarith [hμ.1]
    have hA : muA ≠ 0 := hmuA.ne'
    have hx1 : Real.exp (-(muA * L * (1 + μ) / μ)) = Real.exp (-((muA + 0) * L * ((μ + 1) / μ))) := by
      congr 1; ring
    have hx2 : Real.exp (-((muA + 0) * L * ((μ - 1) / μ))) * Real.exp (-((muA + 0) * L / μ))
        = Real.exp (-(muA * L)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have hx3 : Real.exp (-(muA * L / μ)) = Real.exp (-((muA + 0) * L / μ)) := by
      congr 1; ring
    simp only [F1, F2]
    rw [hx1, hx3, add_zero]
    rw [add_zero] at hx2
    rw [← hx2]
    generalize Real.exp (-(muA * L * ((μ + 1) / μ))) = A
    generalize Real.exp (-(muA * L * ((μ - 1) / μ))) = D
    generalize Real.exp (-(muA * L / μ)) = C
    have h1μ : 1 + μ ≠ 0 := by linarith [hμ.1]
    field_simp
    ring
  have key : P0 * -(Real.exp (-((muA + 0) * L)) * -(1 * L) + K1 0 + K2 0)
      = -(P0 / muA) * criticalLHS p (muA * L) := by
    rw [hcrit, add_zero]; field_simp; ring
  rw [key]
  simp [hP0.ne', hmuA.ne']
