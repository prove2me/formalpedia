-- Prove2me | solution 1 for Arxiv2405_15536.kappa_objective_least_squares_limit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T06:43:47.17609+00:00
-- url     : https://prove2.me/submissions/ddc1bb49-fbfc-47dc-a215-f139b89b3e35

import Mathlib
import Definitions.Def_Arxiv2405_15536_Basic

open MeasureTheory Set Filter Topology

namespace S81L
open Arxiv2405_15536

lemma ns (y : ℝ) (hy : 0 < y) : Real.Gamma (y + 1 / 2) ^ 2 ≤ y * Real.Gamma y ^ 2 := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := y) (t := y + 1) (a := 1/2) (b := 1/2)
    hy (by linarith) (by norm_num) (by norm_num) (by norm_num)
  rw [show 1 / 2 * y + 1 / 2 * (y + 1) = y + 1 / 2 by ring, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have h0 : 0 ≤ Real.Gamma (y + 1 / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  have h2 := pow_le_pow_left₀ h0 h 2
  rw [mul_pow, Real.sq_sqrt (Real.Gamma_pos_of_pos hy).le,
    Real.sq_sqrt (Real.Gamma_pos_of_pos (by linarith)).le, Real.Gamma_add_one hy.ne'] at h2
  linarith

lemma gb (y : ℝ) (hy : 0 < y) : Real.Gamma (y + 1 / 2) ^ 2 ≤ y * Real.Gamma y ^ 2 ∧
    y ^ 2 * Real.Gamma y ^ 2 ≤ (y + 1 / 2) * Real.Gamma (y + 1 / 2) ^ 2 := by
  refine ⟨ns y hy, ?_⟩
  have h := ns (y + 1 / 2) (by linarith)
  rw [show y + 1 / 2 + 1 / 2 = y + 1 by ring, Real.Gamma_add_one hy.ne'] at h
  nlinarith [h]

lemma rat (c : ℝ) : Tendsto (fun x : ℝ => x / (x - c)) atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => 1 / (1 - c * x⁻¹)) atTop (𝓝 (1 / (1 - c * 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_atTop_zero)) (by simp)
  rw [show (1:ℝ) / (1 - c * 0) = 1 by simp] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (max c 0)] with x hx
  have hx0 : 0 < x := lt_of_le_of_lt (le_max_right _ _) hx
  have hxc : x - c ≠ 0 := by linarith [le_max_left c 0]
  have : 1 - c * x⁻¹ = (x - c) / x := by field_simp
  rw [this]; field_simp

lemma X_tend : Tendsto (fun κ : ℝ => |2 * κ|⁻¹) (𝓝[≠] 0) atTop := by
  have h : Tendsto (fun κ : ℝ => |2 * κ|) (𝓝[≠] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall (fun κ hκ => ?_)⟩
    · have : Tendsto (fun κ : ℝ => |2 * κ|) (𝓝 0) (𝓝 (|2 * 0|)) :=
        ((continuous_const.mul continuous_id).abs).tendsto 0
      simp only [mul_zero, abs_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact show 0 < |2 * κ| from abs_pos.2 (mul_ne_zero two_ne_zero hκ)
  exact tendsto_inv_nhdsGT_zero.comp h

lemma K1 : Tendsto (fun x : ℝ => x * (Real.Gamma (x - 3 / 4) * Real.Gamma (x + 1 / 4) /
    (Real.Gamma (x + 3 / 4) * Real.Gamma (x - 1 / 4)))) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (rat (1 / 4)) (rat (3 / 4)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    have hy : 0 < x - 3 / 4 := by linarith
    obtain ⟨b1, _⟩ := gb (x - 3 / 4) hy
    rw [show x + 1 / 4 = (x - 3 / 4) + 1 by ring, show x + 3 / 4 = ((x - 3 / 4) + 1 / 2) + 1 by ring,
      show x - 1 / 4 = (x - 3 / 4) + 1 / 2 by ring, Real.Gamma_add_one hy.ne', Real.Gamma_add_one (by linarith)]
    set y := x - 3 / 4
    have hG := Real.Gamma_pos_of_pos hy
    have hH := Real.Gamma_pos_of_pos (show 0 < y + 1 / 2 by linarith)
    set G := Real.Gamma y
    set H := Real.Gamma (y + 1 / 2)
    have e : x * (G * (y * G) / ((y + 1 / 2) * H * H)) = x * (y * G ^ 2) / ((y + 1 / 2) * H ^ 2) := by ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left b1 (show 0 ≤ x * (y + 1 / 2) by positivity)
    nlinarith [this]
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    have hy : 0 < x - 3 / 4 := by linarith
    obtain ⟨_, b2⟩ := gb (x - 3 / 4) hy
    rw [show x + 1 / 4 = (x - 3 / 4) + 1 by ring, show x + 3 / 4 = ((x - 3 / 4) + 1 / 2) + 1 by ring,
      show x - 1 / 4 = (x - 3 / 4) + 1 / 2 by ring, Real.Gamma_add_one hy.ne', Real.Gamma_add_one (by linarith)]
    set y := x - 3 / 4
    have hG := Real.Gamma_pos_of_pos hy
    have hH := Real.Gamma_pos_of_pos (show 0 < y + 1 / 2 by linarith)
    set G := Real.Gamma y
    set H := Real.Gamma (y + 1 / 2)
    have e : x * (G * (y * G) / ((y + 1 / 2) * H * H)) = x * (y * G ^ 2) / ((y + 1 / 2) * H ^ 2) := by ring
    rw [e, div_le_div_iff₀ (by positivity) hy]
    have := mul_le_mul_of_nonneg_left b2 (show 0 ≤ x by positivity)
    nlinarith [this]

lemma K2 : Tendsto (fun x : ℝ => Real.sqrt x * (Real.Gamma (x - 1 / 4) / Real.Gamma (x + 1 / 4))) atTop (𝓝 1) := by
  have hup : Tendsto (fun x : ℝ => x / (x - 1 / 4) * ((x + 1 / 4) / ((x + 1 / 4) - 1 / 2))) atTop (𝓝 (1 * 1)) :=
    (rat (1 / 4)).mul ((rat (1 / 2)).comp (tendsto_atTop_add_const_right _ (1 / 4) tendsto_id))
  rw [mul_one] at hup
  have hQ : Tendsto (fun x : ℝ => x * (Real.Gamma (x - 1 / 4) / Real.Gamma (x + 1 / 4)) ^ 2) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (rat (1 / 4)) hup ?_ ?_
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      have hu : 0 < x - 1 / 4 := by linarith
      obtain ⟨b1, _⟩ := gb (x - 1 / 4) hu
      rw [show x + 1 / 4 = (x - 1 / 4) + 1 / 2 by ring]
      have hH := Real.Gamma_pos_of_pos (show 0 < x - 1 / 4 + 1 / 2 by linarith)
      have hG := Real.Gamma_pos_of_pos hu
      rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ hu (by positivity)]
      have := mul_le_mul_of_nonneg_left b1 (show 0 ≤ x by positivity)
      nlinarith [this]
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      have hu : 0 < x - 1 / 4 := by linarith
      obtain ⟨_, b2⟩ := gb (x - 1 / 4) hu
      rw [show x + 1 / 4 = (x - 1 / 4) + 1 / 2 by ring, show x - 1 / 4 + 1 / 2 - 1 / 2 = x - 1 / 4 by ring]
      have hH := Real.Gamma_pos_of_pos (show 0 < x - 1 / 4 + 1 / 2 by linarith)
      have hG := Real.Gamma_pos_of_pos hu
      rw [div_pow, ← mul_div_assoc, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left b2 (show 0 ≤ x by positivity)
      nlinarith [this]
  have := (Real.continuous_sqrt.tendsto 1).comp hQ
  rw [Real.sqrt_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  have hG := Real.Gamma_pos_of_pos (show 0 < x - 1 / 4 by linarith)
  have hH := Real.Gamma_pos_of_pos (show 0 < x + 1 / 4 by linarith)
  simp only [Function.comp]
  rw [Real.sqrt_mul (by linarith), Real.sqrt_sq (by positivity)]

lemma EK (a : ℝ → ℝ) (A : ℝ) (ha : Tendsto a (𝓝[≠] 0) (𝓝 A)) :
    Tendsto (fun κ => expKappa κ (a κ)) (𝓝[≠] 0) (𝓝 (Real.exp A)) := by
  have hd : ContinuousAt (dslope Real.arsinh 0) 0 :=
    continuousAt_dslope_same.2 (Real.hasDerivAt_arsinh 0).differentiableAt
  have h1 : dslope Real.arsinh 0 0 = 1 := by
    rw [dslope_same, (Real.hasDerivAt_arsinh 0).deriv]; simp
  have hka : Tendsto (fun κ => κ * a κ) (𝓝[≠] 0) (𝓝 0) := by
    have := (tendsto_id.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ) (a := (0:ℝ)))).mul ha
    simpa using this
  have hm : Tendsto (fun κ => Real.exp (a κ * dslope Real.arsinh 0 (κ * a κ))) (𝓝[≠] 0) (𝓝 (Real.exp (A * 1))) := by
    refine (Real.continuous_exp.tendsto _).comp (ha.mul ?_)
    rw [← h1]; exact hd.tendsto.comp hka
  rw [mul_one] at hm
  refine hm.congr' (eventually_nhdsWithin_of_forall (fun κ hκ => ?_))
  have hκ : κ ≠ 0 := hκ
  simp only [expKappa, if_neg hκ]
  set z := κ * a κ
  have hz := sub_smul_dslope Real.arsinh 0 z
  simp only [sub_zero, Real.arsinh_zero, smul_eq_mul] at hz
  have habs : |z| < Real.sqrt (1 + z ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have hpos : 0 < Real.sqrt (1 + κ ^ 2 * a κ ^ 2) + κ * a κ := by
    rw [show κ ^ 2 * a κ ^ 2 = z ^ 2 by simp only [z]; ring]
    linarith [neg_abs_le z]
  rw [Real.rpow_def_of_pos hpos]
  congr 1
  have : Real.log (Real.sqrt (1 + κ ^ 2 * a κ ^ 2) + κ * a κ) = Real.arsinh z := by
    rw [Real.arsinh, show κ ^ 2 * a κ ^ 2 = z ^ 2 by simp only [z]; ring, add_comm]
  rw [this, ← hz]
  simp only [z]
  field_simp


lemma hβ : Tendsto betaKappa (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have ha : Tendsto (fun κ : ℝ => |κ|) (𝓝[≠] 0) (𝓝 0) :=
    (continuous_abs.tendsto' 0 0 abs_zero).mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun κ : ℝ => (1 + |κ| / 2) / (1 + 3 / 2 * |κ|)) (𝓝[≠] 0) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1:ℝ)).add (ha.div_const 2)).div
      (tendsto_const_nhds (x := (1:ℝ)).add (ha.const_mul (3 / 2))) (by norm_num)
    rw [show ((1:ℝ) + 0 / 2) / (1 + 3 / 2 * 0) = 1 by norm_num] at this
    exact this
  have h3 := ((K1.comp X_tend).mul hc).div_const 2
  rw [show (1:ℝ) * 1 / 2 = 1 / 2 by norm_num] at h3
  refine h3.congr' (eventually_nhdsWithin_of_forall (fun κ hκ => ?_))
  have hκ : κ ≠ 0 := hκ
  simp only [Function.comp, betaKappa, if_neg hκ, one_div]
  ring

lemma abs_arsinh_le (z : ℝ) : |Real.arsinh z| ≤ |z| := by
  have pos : ∀ w : ℝ, 0 ≤ w → |Real.arsinh w| ≤ |w| := fun w hw => by
    rw [abs_of_nonneg (Real.arsinh_nonneg_iff.2 hw), abs_of_nonneg hw]
    calc Real.arsinh w ≤ Real.arsinh (Real.sinh w) := Real.arsinh_le_arsinh.2 (Real.self_le_sinh_iff.2 hw)
      _ = w := Real.arsinh_sinh w
  rcases le_total 0 z with h | h
  · exact pos z h
  · have := pos (-z) (by linarith)
    rwa [Real.arsinh_neg, abs_neg, abs_neg] at this

lemma lossEq (κ : ℝ) (hκ : κ ≠ 0) (ε : ℝ) :
    lossKappa κ ε = -(Real.arsinh (κ * (-betaKappa κ * ε ^ 2)) / κ) := by
  unfold lossKappa expKappa
  rw [if_neg hκ]
  set a := -betaKappa κ * ε ^ 2
  set z := κ * a
  have habs : |z| < Real.sqrt (1 + z ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have hpos : 0 < Real.sqrt (1 + κ ^ 2 * a ^ 2) + κ * a := by
    rw [show κ ^ 2 * a ^ 2 = z ^ 2 by simp only [z]; ring]
    linarith [neg_abs_le z]
  rw [Real.rpow_def_of_pos hpos, Real.log_exp]
  have : Real.log (Real.sqrt (1 + κ ^ 2 * a ^ 2) + κ * a) = Real.arsinh z := by
    rw [Real.arsinh, show κ ^ 2 * a ^ 2 = z ^ 2 by simp only [z]; ring, add_comm]
  rw [this]; ring

lemma lossLim (ε : ℝ) : Tendsto (fun κ => lossKappa κ ε) (𝓝[≠] 0) (𝓝 (ε ^ 2 / 2)) := by
  have hd : ContinuousAt (dslope Real.arsinh 0) 0 :=
    continuousAt_dslope_same.2 (Real.hasDerivAt_arsinh 0).differentiableAt
  have h1 : dslope Real.arsinh 0 0 = 1 := by
    rw [dslope_same, (Real.hasDerivAt_arsinh 0).deriv]; simp
  have ha : Tendsto (fun κ => -betaKappa κ * ε ^ 2) (𝓝[≠] 0) (𝓝 (-(1 / 2) * ε ^ 2)) := (hβ.neg).mul_const _
  have hka : Tendsto (fun κ => κ * (-betaKappa κ * ε ^ 2)) (𝓝[≠] 0) (𝓝 0) := by
    have := (tendsto_id.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ) (a := (0:ℝ)))).mul ha
    simpa using this
  have hm : Tendsto (fun κ => -((-betaKappa κ * ε ^ 2) * dslope Real.arsinh 0 (κ * (-betaKappa κ * ε ^ 2))))
      (𝓝[≠] 0) (𝓝 (-((-(1 / 2) * ε ^ 2) * 1))) := by
    refine (ha.mul ?_).neg
    rw [← h1]; exact hd.tendsto.comp hka
  rw [show -((-(1 / 2) * ε ^ 2) * 1) = ε ^ 2 / 2 by ring] at hm
  refine hm.congr' (eventually_nhdsWithin_of_forall (fun κ hκ => ?_))
  have hκ : κ ≠ 0 := hκ
  show _ = lossKappa κ ε
  rw [lossEq κ hκ]
  have hz := sub_smul_dslope Real.arsinh 0 (κ * (-betaKappa κ * ε ^ 2))
  simp only [sub_zero, Real.arsinh_zero, smul_eq_mul] at hz
  rw [← hz]; field_simp

end S81L

open Arxiv2405_15536 S81L in
theorem solution {S R : Type*} [Fintype S] [Fintype R] (T : ℝ)
    (e : S → R → ℝ → ℝ) (he : ∀ s r, IntegrableOn (fun t => e s r t ^ 2) (Set.Icc 0 T)) :
    Tendsto (fun κ => phiKappa κ T e) (𝓝[≠] 0) (𝓝 (phi0 T e)) := by
  have key : ∀ s r, Tendsto (fun κ => ∫ t in Icc 0 T, lossKappa κ (e s r t)) (𝓝[≠] 0)
      (𝓝 (∫ t in Icc 0 T, e s r t ^ 2 / 2)) := by
    intro s r
    apply tendsto_integral_filter_of_dominated_convergence (fun t => e s r t ^ 2)
    · refine eventually_nhdsWithin_of_forall (fun κ hκ => ?_)
      have hκ : κ ≠ 0 := hκ
      rw [show (fun t => lossKappa κ (e s r t)) =
          (fun u => -(Real.arsinh (κ * (-betaKappa κ * u)) / κ)) ∘ (fun t => e s r t ^ 2) from
          funext fun t => lossEq κ hκ _]
      exact ((Real.continuous_arsinh.comp (continuous_const.mul (continuous_const.mul continuous_id))).div_const κ).neg.comp_aestronglyMeasurable
        (he s r).aestronglyMeasurable
    · filter_upwards [hβ.eventually (Ioo_mem_nhds (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)),
        self_mem_nhdsWithin] with κ hb hκ
      have hκ : κ ≠ 0 := hκ
      refine Filter.Eventually.of_forall (fun t => ?_)
      rw [lossEq κ hκ, Real.norm_eq_abs, abs_neg, abs_div, div_le_iff₀ (abs_pos.2 hκ)]
      refine (abs_arsinh_le _).trans ?_
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos hb.1, abs_of_nonneg (sq_nonneg (e s r t))]
      have := hb.2
      nlinarith [abs_nonneg κ, sq_nonneg (e s r t), mul_nonneg (abs_nonneg κ) (sq_nonneg (e s r t))]
    · exact he s r
    · exact Filter.Eventually.of_forall (fun t => lossLim (e s r t))
  have h := tendsto_finsetSum (Finset.univ : Finset S) (fun s _ =>
    tendsto_finsetSum (Finset.univ : Finset R) (fun r _ => key s r))
  have eq : phi0 T e = ∑ s, ∑ r, ∫ t in Icc 0 T, e s r t ^ 2 / 2 := by
    unfold phi0
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [integral_div]; ring
  rw [eq]
  exact h
