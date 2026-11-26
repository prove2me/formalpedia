-- Prove2me | solution 1 for Arxiv2405_15536.kappa_gaussian_fat_tails
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T02:52:00.196289+00:00
-- url     : https://prove2.me/submissions/896ff863-fb18-46a1-9572-c993ef9df7c6

import Mathlib
import Definitions.Def_Arxiv2405_15536_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology Asymptotics

namespace S76FT
open Arxiv2405_15536

lemma beta_pos (κ : ℝ) (h0 : 0 < κ) (hκ : κ < 2 / 3) : 0 < betaKappa κ := by
  have h : κ ≠ 0 := h0.ne'
  have ha : 0 < |κ| := abs_pos.2 h
  have h2 : |2 * κ| = 2 * |κ| := by rw [abs_mul]; norm_num
  have hk : |κ| < 2 / 3 := by rw [abs_of_pos h0]; exact hκ
  have hA : 3 / 4 < 1 / |2 * κ| := by
    rw [h2, lt_div_iff₀ (by positivity)]; nlinarith
  unfold betaKappa
  rw [if_neg h]
  have g1 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| - 3 / 4 by linarith)
  have g2 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| + 1 / 4 by linarith)
  have g3 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| + 3 / 4 by linarith)
  have g4 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| - 1 / 4 by linarith)
  have : 0 < |2 * κ| := by rw [h2]; positivity
  positivity

lemma z_pos (κ : ℝ) (h0 : 0 < κ) (hκ : κ < 2 / 3) : 0 < zKappa κ := by
  unfold zKappa
  have h : κ ≠ 0 := h0.ne'
  rw [if_neg h]
  have ha : 0 < |κ| := abs_pos.2 h
  have h2 : |2 * κ| = 2 * |κ| := by rw [abs_mul]; norm_num
  have hk : |κ| < 2 / 3 := by rw [abs_of_pos h0]; exact hκ
  have hA : 3 / 4 < 1 / |2 * κ| := by
    rw [h2, lt_div_iff₀ (by positivity)]; nlinarith
  have hb := beta_pos κ h0 hκ
  have g2 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| + 1 / 4 by linarith)
  have g4 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| - 1 / 4 by linarith)
  have h3 : 0 < Real.sqrt (Real.pi / betaKappa κ) := Real.sqrt_pos.2 (div_pos Real.pi_pos hb)
  have h4 : 0 < |2 * κ| := by rw [h2]; positivity
  have h5 : 0 < |2 * κ| ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos h4 _
  positivity

/-- closed form: exp_κ(-βε²) = (√(1+a²)+a)^(-1/κ), a = κβε² -/
lemma F_eq (κ : ℝ) (h0 : 0 < κ) (ε : ℝ) :
    expKappa κ (-betaKappa κ * ε ^ 2) =
      (Real.sqrt (1 + (κ * betaKappa κ * ε ^ 2) ^ 2) + κ * betaKappa κ * ε ^ 2) ^ (-1 / κ) := by
  unfold expKappa
  rw [if_neg h0.ne']
  set a := κ * betaKappa κ * ε ^ 2
  have e1 : 1 + κ ^ 2 * (-betaKappa κ * ε ^ 2) ^ 2 = 1 + a ^ 2 := by simp only [a]; ring
  have e2 : κ * (-betaKappa κ * ε ^ 2) = -a := by simp only [a]; ring
  rw [e1, e2]
  have hs : 0 ≤ Real.sqrt (1 + a ^ 2) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (1 + a ^ 2) ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hpos : 0 < Real.sqrt (1 + a ^ 2) + a := by
    have h1 : |a| < Real.sqrt (1 + a ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; apply Real.sqrt_lt_sqrt (sq_nonneg _); linarith
    have := neg_abs_le a; linarith
  have hinv : Real.sqrt (1 + a ^ 2) + -a = (Real.sqrt (1 + a ^ 2) + a)⁻¹ := by
    field_simp; nlinarith
  rw [hinv, Real.inv_rpow hpos.le, neg_div, Real.rpow_neg hpos.le]

lemma base_pos (a : ℝ) : 0 < Real.sqrt (1 + a ^ 2) + a := by
  have h1 : |a| < Real.sqrt (1 + a ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; apply Real.sqrt_lt_sqrt (sq_nonneg _); linarith
  have := neg_abs_le a; linarith

lemma base_le (a : ℝ) (ha : 0 ≤ a) : Real.sqrt (1 + a ^ 2) + a ≤ 2 * a + 1 := by
  have : Real.sqrt (1 + a ^ 2) ≤ a + 1 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  linarith

lemma base_ge (a : ℝ) (ha : 0 ≤ a) : 2 * a ≤ Real.sqrt (1 + a ^ 2) + a := by
  have : a ≤ Real.sqrt (1 + a ^ 2) := by
    apply Real.le_sqrt_of_sq_le; linarith
  linarith

lemma F_lo (κ : ℝ) (h0 : 0 < κ) (hκ : κ < 2 / 3) (ε : ℝ) :
    (2 * (κ * betaKappa κ * ε ^ 2) + 1) ^ (-1 / κ) ≤ expKappa κ (-betaKappa κ * ε ^ 2) := by
  rw [F_eq κ h0]
  have hb := beta_pos κ h0 hκ
  have ha : 0 ≤ κ * betaKappa κ * ε ^ 2 := by positivity
  apply Real.rpow_le_rpow_of_nonpos (base_pos _) (base_le _ ha)
  rw [neg_div]; exact neg_nonpos.2 (by positivity)

lemma F_hi (κ : ℝ) (h0 : 0 < κ) (hκ : κ < 2 / 3) (ε : ℝ) (hε : ε ≠ 0) :
    expKappa κ (-betaKappa κ * ε ^ 2) ≤ (2 * (κ * betaKappa κ * ε ^ 2)) ^ (-1 / κ) := by
  rw [F_eq κ h0]
  have hb := beta_pos κ h0 hκ
  have ha : 0 < κ * betaKappa κ * ε ^ 2 := by positivity
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (base_ge _ ha.le)
  rw [neg_div]; exact neg_nonpos.2 (by positivity)

lemma sq_tendsto : Tendsto (fun ε : ℝ => ε ^ 2) (cocompact ℝ) atTop := by
  have h := (tendsto_norm_cocompact_atTop (E := ℝ))
  have : (fun ε : ℝ => ε ^ 2) = (fun x => x ^ 2) ∘ (fun ε : ℝ => ‖ε‖) := by
    funext ε; simp [Real.norm_eq_abs, sq_abs]
  rw [this]
  exact (tendsto_pow_atTop (by norm_num)).comp h

lemma ne_zero_ev : ∀ᶠ ε : ℝ in cocompact ℝ, ε ≠ 0 := by
  have := sq_tendsto.eventually_gt_atTop 0
  filter_upwards [this] with ε h
  rintro rfl; simp at h

end S76FT

open Arxiv2405_15536 S76FT in
theorem solution (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ < 2 / 3) :
    IsEquivalent (cocompact ℝ) (fun ε => expKappa κ (-betaKappa κ * ε ^ 2))
      (fun ε => (2 * κ * betaKappa κ * ε ^ 2) ^ (-1 / κ)) ∧
    Tendsto (fun ε => kappaGaussian κ ε / ProbabilityTheory.gaussianPDFReal 0 1 ε)
      (cocompact ℝ) atTop ∧
    (∀ κ' : ℝ, κ < κ' → κ' < 2 / 3 →
      Tendsto (fun ε => kappaGaussian κ' ε / kappaGaussian κ ε) (cocompact ℝ) atTop) := by
  have hb := beta_pos κ hκ0 hκ
  refine ⟨?_, ?_, ?_⟩
  · -- part 1
    apply isEquivalent_of_tendsto_one
    -- ratio = ((√(1+a²)+a)/(2a))^(-1/κ)
    set c := κ * betaKappa κ with hc
    have hcpos : 0 < c := by positivity
    have ha : Tendsto (fun ε : ℝ => c * ε ^ 2) (cocompact ℝ) atTop :=
      sq_tendsto.const_mul_atTop hcpos
    -- g(a) = (√(1+a²)+a)/(2a) → 1
    have hg : Tendsto (fun a : ℝ => (Real.sqrt (1 + a ^ 2) + a) / (2 * a)) atTop (𝓝 1) := by
      have hup : Tendsto (fun a : ℝ => 1 + (2 * a)⁻¹) atTop (𝓝 1) := by
        have := (tendsto_inv_atTop_zero.comp ((tendsto_id).const_mul_atTop (by norm_num : (0:ℝ) < 2)))
        simpa using this.const_add 1
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with a h
        rw [le_div_iff₀ (by positivity)]; linarith [base_ge a h.le]
      · filter_upwards [eventually_gt_atTop 0] with a h
        rw [div_le_iff₀ (by positivity)]
        have := base_le a h.le
        have : (1 + (2 * a)⁻¹) * (2 * a) = 2 * a + 1 := by field_simp
        linarith
    have hg2 := (hg.rpow_const (p := -1 / κ) (Or.inl one_ne_zero)).comp ha
    rw [Real.one_rpow] at hg2
    refine hg2.congr' ?_
    filter_upwards [ne_zero_ev] with ε hε
    simp only [Function.comp, Pi.div_apply]
    rw [F_eq κ hκ0]
    have hε2 : 0 < c * ε ^ 2 := by positivity
    rw [Real.div_rpow (base_pos _).le (by positivity)]
    congr 2; ring
  · -- part 2
    have hZ := z_pos κ hκ0 hκ
    set c := 2 * (κ * betaKappa κ) with hc
    have hcpos : 0 < c := by positivity
    set p := 1 / κ with hp
    set K := (2 * c) ^ (-p) * Real.sqrt (2 * Real.pi) / zKappa κ / Real.exp (1 / (2 * c)) with hK
    have hKpos : 0 < K := by
      have : 0 < (2 * c) ^ (-p) := Real.rpow_pos_of_pos (by positivity) _
      positivity
    have hx : Tendsto (fun ε : ℝ => (c * ε ^ 2 + 1) / (2 * c)) (cocompact ℝ) atTop := by
      apply Tendsto.atTop_div_const (by positivity)
      exact tendsto_atTop_add_const_right _ 1 (sq_tendsto.const_mul_atTop hcpos)
    have hmain := ((tendsto_exp_div_rpow_atTop p).comp hx).const_mul_atTop hKpos
    refine tendsto_atTop_mono' _ ?_ hmain
    filter_upwards with ε
    simp only [Function.comp]
    have hlo := F_lo κ hκ0 hκ ε
    have e1 : (2 * (κ * betaKappa κ * ε ^ 2) + 1) = c * ε ^ 2 + 1 := by simp only [c]; ring
    rw [e1] at hlo
    set x := (c * ε ^ 2 + 1) / (2 * c) with hxdef
    have hxpos : 0 < x := by positivity
    have hu : c * ε ^ 2 + 1 = (2 * c) * x := by simp only [x]; field_simp
    rw [hu, Real.mul_rpow (by positivity) hxpos.le] at hlo
    have hgauss : ProbabilityTheory.gaussianPDFReal 0 1 ε =
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-ε ^ 2 / 2) := by
      rw [ProbabilityTheory.gaussianPDFReal]; simp
    unfold kappaGaussian
    rw [hgauss]
    have hE : Real.exp (-ε ^ 2 / 2) = Real.exp (1 / (2 * c)) * (Real.exp x)⁻¹ := by
      rw [← Real.exp_neg, ← Real.exp_add]; congr 1; simp only [x]; field_simp; ring
    rw [hE]
    have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hxpos _
    have hxn : x ^ (-1 / κ) = (x ^ p)⁻¹ := by rw [neg_div, Real.rpow_neg hxpos.le]
    rw [hxn] at hlo
    have hex : 0 < Real.exp x := Real.exp_pos x
    have hec : 0 < Real.exp (1 / (2 * c)) := Real.exp_pos _
    have h2c : (2 * c) ^ (-1 / κ) = (2 * c) ^ (-p) := by rw [neg_div]
    rw [h2c] at hlo
    rw [hK]
    rw [show (2 * c) ^ (-p) * Real.sqrt (2 * Real.pi) / zKappa κ / Real.exp (1 / (2 * c)) *
        (Real.exp x / x ^ p) =
        ((2 * c) ^ (-p) * (x ^ p)⁻¹) / zKappa κ /
          ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (1 / (2 * c)) * (Real.exp x)⁻¹)) by
      field_simp]
    gcongr
  · -- part 3
    intro κ' h1 h2
    have h0' : 0 < κ' := by linarith
    have hb' := beta_pos κ' h0' h2
    have hZ := z_pos κ hκ0 hκ
    have hZ' := z_pos κ' h0' h2
    set c := 2 * (κ * betaKappa κ) with hc
    set c' := 2 * (κ' * betaKappa κ') with hc'
    have hcpos : 0 < c := by positivity
    have hcpos' : 0 < c' := by positivity
    set K := zKappa κ / zKappa κ' * (c' + 1) ^ (-1 / κ') * c ^ (1 / κ) with hK
    have hKpos : 0 < K := by
      have : 0 < (c' + 1) ^ (-1 / κ') := Real.rpow_pos_of_pos (by positivity) _
      have : 0 < c ^ (1 / κ) := Real.rpow_pos_of_pos hcpos _
      positivity
    have hq : 0 < 1 / κ - 1 / κ' := by
      rw [sub_pos]; exact one_div_lt_one_div_of_lt hκ0 h1
    have hmain := ((tendsto_rpow_atTop hq).comp sq_tendsto).const_mul_atTop hKpos
    refine tendsto_atTop_mono' _ ?_ hmain
    filter_upwards [sq_tendsto.eventually_ge_atTop 1] with ε hε1
    have hε : ε ≠ 0 := by rintro rfl; norm_num at hε1
    simp only [Function.comp]
    set t := ε ^ 2 with ht
    have htpos : 0 < t := by positivity
    have hlo := F_lo κ' h0' h2 ε
    have hhi := F_hi κ hκ0 hκ ε hε
    have e1 : (2 * (κ' * betaKappa κ' * ε ^ 2) + 1) = c' * t + 1 := by simp only [c', t]; ring
    have e2 : (2 * (κ * betaKappa κ * ε ^ 2)) = c * t := by simp only [c, t]; ring
    rw [e1] at hlo; rw [e2] at hhi
    -- (c' t + 1)^(-1/κ') ≥ ((c'+1) t)^(-1/κ')
    have hlo2 : ((c' + 1) * t) ^ (-1 / κ') ≤ (c' * t + 1) ^ (-1 / κ') := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith)
      rw [neg_div]; exact neg_nonpos.2 (by positivity)
    rw [Real.mul_rpow (by positivity) htpos.le] at hlo2
    rw [Real.mul_rpow hcpos.le htpos.le] at hhi
    have hFpos : 0 < expKappa κ (-betaKappa κ * ε ^ 2) := by
      rw [F_eq κ hκ0]; exact Real.rpow_pos_of_pos (base_pos _) _
    have hA : 0 < (c' + 1) ^ (-1 / κ') := Real.rpow_pos_of_pos (by positivity) _
    have hB : 0 < t ^ (-1 / κ') := Real.rpow_pos_of_pos htpos _
    have hC : 0 < c ^ (-1 / κ) := Real.rpow_pos_of_pos hcpos _
    have hD : 0 < t ^ (-1 / κ) := Real.rpow_pos_of_pos htpos _
    -- t^(1/κ - 1/κ') = t^(-1/κ') / t^(-1/κ)
    have htq : t ^ (1 / κ - 1 / κ') = t ^ (-1 / κ') / t ^ (-1 / κ) := by
      rw [← Real.rpow_sub htpos]; congr 1; ring
    have hcq : c ^ (1 / κ) = (c ^ (-1 / κ))⁻¹ := by
      rw [← Real.rpow_neg hcpos.le]; congr 1; ring
    unfold kappaGaussian
    rw [htq, hK, hcq]
    have hnum : (c' + 1) ^ (-1 / κ') * t ^ (-1 / κ') ≤ expKappa κ' (-betaKappa κ' * ε ^ 2) :=
      hlo2.trans hlo
    calc zKappa κ / zKappa κ' * (c' + 1) ^ (-1 / κ') * (c ^ (-1 / κ))⁻¹ *
          (t ^ (-1 / κ') / t ^ (-1 / κ))
        = ((c' + 1) ^ (-1 / κ') * t ^ (-1 / κ')) / zKappa κ' /
            ((c ^ (-1 / κ) * t ^ (-1 / κ)) / zKappa κ) := by
          field_simp
      _ ≤ expKappa κ' (-betaKappa κ' * ε ^ 2) / zKappa κ' /
            (expKappa κ (-betaKappa κ * ε ^ 2) / zKappa κ) := by
          gcongr
          exact div_nonneg (by linarith [mul_pos hA hB]) hZ'.le
