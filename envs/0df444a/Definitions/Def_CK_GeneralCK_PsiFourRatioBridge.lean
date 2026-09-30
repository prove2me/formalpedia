-- Prove2me | Definitions.Def_CK_GeneralCK_PsiFourRatioBridge
-- name    : CK_GeneralCK_PsiFourRatioBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:58:12.067984+00:00
-- url     : https://prove2.me/theorems/e08439f7-db8e-45c4-8668-f69b850d1e19
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiFourRatioBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiFourRatioBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiFourRatioBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiFourRatioBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiFourRatioBridge.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneSymmetric
import Definitions.Def_CK_GeneralCK_PsiLargerEntropyLaw

-- ===== source module GeneralCK.PsiFourRatioBridge =====
section

/-! Retained-child bridge at low entropy for ratios between four and eight. -/

namespace GeneralCK.PsiFourRatioBridge
open Set PsiChildEntropyCoupling PsiSignedSplit
open Certificates.Mixed Certificates.Mixed.Tails

private theorem entropy_natural_upper {p : ℝ} (_hp : 0 < p) (hp1 : p < 1) :
    H p * Real.log 2 ≤ p * Real.log p⁻¹ + p := by
  have hc : 0 < 1 - p := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hc)
  have hh := mul_le_mul_of_nonneg_left h hc.le
  have he : (1 - p) * ((1 - p)⁻¹ - 1) = p := by field_simp; ring
  rw [he] at hh
  rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
  linarith

private theorem entropy_natural_lower {p : ℝ} (_hp : 0 < p) (hp1 : p < 1) :
    p * Real.log p⁻¹ + p * (1 - p) ≤ H p * Real.log 2 := by
  have hc : 0 < 1 - p := by linarith
  have h := Real.log_le_sub_one_of_pos hc
  have hl : p ≤ Real.log (1 - p)⁻¹ := by rw [Real.log_inv]; linarith
  have hh := mul_le_mul_of_nonneg_left hl hc.le
  rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
  nlinarith

theorem contact_four_bracket :
    (1 : ℝ) / 32 ≤ radialContact 4 1 ∧ radialContact 4 1 ≤ 1 / 22 := by
  have hL : (2 / 3 : ℝ) < Real.log 2 := by linarith [log_two_gt_69]
  have hLu : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  constructor
  · apply (le_radialContact_iff (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2
    have h := entropy_natural_upper (p := 1 / 32) (by norm_num) (by norm_num)
    have hlog : Real.log ((1 / 32 : ℝ)⁻¹) = 5 * Real.log 2 := by
      norm_num
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [hlog] at h
    have hH : H (1 / 32 : ℝ) ≤ 13 / 64 := by
      nlinarith [mul_nonneg log_two_pos.le (sub_nonneg.mpr (H_le_one (1 / 32)))]
    norm_num
    linarith
  · apply (radialContact_le_iff (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2
    have h := entropy_natural_lower (p := 1 / 22) (by norm_num) (by norm_num)
    have hlog : 4 * Real.log 2 ≤ Real.log ((1 / 22 : ℝ)⁻¹) := by
      have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 16) (by norm_num : (16 : ℝ) ≤ 22)
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow] at hl
      norm_num at hl ⊢
      exact hl
    have hH : (5 / 22 : ℝ) ≤ H (1 / 22) := by
      by_contra hn
      have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hn) log_two_pos
      nlinarith
    norm_num
    linarith

theorem radial_slope_lt_fifteen_halves {v : ℝ}
    (hl : 1 / 32 ≤ v) (hu : v ≤ 1 / 22) : radialSlope v < 15 / 2 := by
  have hv : 0 < v := by linarith
  have hvh : v < 1 / 2 := by linarith
  have hL : 0 < Real.log 2 := log_two_pos
  have hk := kap_pos hv hvh
  have hc : 0 < 1 - v := by linarith
  have hh0 : 0 ≤ hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_nonneg (H_nonneg hv.le (by linarith)) hL.le
  have hJ : J v < 5 := by
    have hm := J_antitone (by norm_num : (0 : ℝ) < 1 / 32) hvh.le hl
    have ha : J (1 / 32 : ℝ) < 5 := by
      have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 31) (by norm_num : (31 : ℝ) < 32)
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow] at h
      unfold J
      norm_num
      apply (div_lt_iff₀ hL).2
      simpa using h
    exact hm.trans_lt ha
  have he : (69 / 25 : ℝ) ≤ logit v := by
    have hr : (16 : ℝ) ≤ (1 - v) / v := (le_div_iff₀ hv).2 (by linarith)
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hr
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow] at hm
    unfold logit
    nlinarith [log_two_gt_69]
  have he0 : 0 < logit v := by linarith
  have hratio := left_ratio_bound hv hu
  have hratio' : hn v / ((4 * v * (1 - v)) * kap v) ≤
      (10 / 19 : ℝ) * (1 + (20 / 19) / (69 / 25)) := by
    apply hratio.trans
    gcongr
  have hratio0 : 0 ≤ hn v / ((4 * v * (1 - v)) * kap v) := by positivity
  have hcoef : 2 * (1 - 2 * v) / Real.log 2 ≤ (200 / 69 : ℝ) := by
    apply (div_le_iff₀ hL).2
    nlinarith [log_two_gt_69]
  have hh := mul_le_mul hcoef hratio' hratio0 (by norm_num : (0 : ℝ) ≤ 200 / 69)
  have hid : (2 * (1 - 2 * v) / Real.log 2) *
      (hn v / ((4 * v * (1 - v)) * kap v)) =
      (1 - 2 * v) * hn v / (2 * Real.log 2 * v * (1 - v) * kap v) := by
    field_simp
    ring
  rw [hid] at hh
  have hcorrection : (1 - 2 * v) * hn v /
      (2 * Real.log 2 * v * (1 - v) * kap v) < 5 / 2 :=
    hh.trans_lt (by norm_num)
  unfold radialSlope
  linarith

theorem radial_ratio_le_fifteen_sixteenths {x : ℝ} (hx : 4 ≤ x) :
    deriv (fun r => F r 1) x / (2 * x) ≤ 15 / 16 := by
  have hm := antitoneOn_F_radius_ratio (by norm_num : (0 : ℝ) < 1)
    (show (4 : ℝ) ∈ Ioi 0 by norm_num) (show x ∈ Ioi 0 by change 0 < x; linarith) hx
  have he : deriv (fun r => F r 1) 4 / (2 * 4) ≤ 15 / 16 := by
    have hd : deriv (fun r => F r 1) 4 < 15 / 2 := by
      rw [deriv_F_radius_slope (by norm_num) (by norm_num)]
      exact radial_slope_lt_fifteen_halves contact_four_bracket.1 contact_four_bracket.2
    norm_num
    linarith
  exact hm.trans he

theorem radial_average_loss {d E : ℝ}
    (hE : 0 < E) (hd : 4 * E ≤ d) (q : ℝ) :
    (F |d - q| E + F |d + q| E) / 2 - F d E ≤ (15 / 16) * (q ^ 2 / E) := by
  have hd0 : 0 < d := by linarith
  have hx : 4 ≤ d / E := (le_div_iff₀ hE).2 hd
  have hb := radial_ratio_le_fifteen_sixteenths hx
  have hh := F_average_difference_le hd0 hE q
  have heq : q ^ 2 / (2 * d) * deriv (fun r => F r E) d =
      (q ^ 2 / E) * (deriv (fun r => F r 1) (d / E) / (2 * (d / E))) := by
    rw [deriv_F_radius_normalize hd0 hE]
    field_simp
  have hp := mul_le_mul_of_nonneg_left hb (show 0 ≤ q ^ 2 / E by positivity)
  rw [heq] at hh
  nlinarith only [hh, hp]

/-- At small mean difference, the retained child entropy curvature alone
pays for the entire signed split loss. No cost imbalance gain is required. -/
theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEi : E ≤ 1 / 1000000)
    (hd4 : 4 * E ≤ d) (hd8 : d ≤ 8 * E)
    (hq : 0 ≤ q) (hqd : q ≤ d) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 20) * (q ^ 2 / E) ≤ F d E := by
  have hqE : q ≤ 8 * E := hqd.trans hd8
  have hgain := eta_parent_gain_small_entropy hE hEi hq hqE
    (PsiLowEntropyRedesign.parent_entropy_le_one hE hEi hq hqE)
  have hr := radial_average_loss hE hd4 q
  rw [abs_of_nonneg (show 0 ≤ d - q by linarith),
    abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
  have hr' : radialLoss d q E ≤ (15 / 16) * (q ^ 2 / E) := by
    unfold radialLoss
    linarith only [hr]
  obtain ⟨hA, hA'⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq hqd
  let c := 1 / (2 * Real.log 2) - 13 * d / 12
  have hc : 1 / 3 ≤ c := by
    have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
      have h := Certificates.PilotData.log_two.2
      norm_num at h
      linarith
    have hbase : (5 / 7 : ℝ) ≤ 1 / (2 * Real.log 2) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
      linarith
    dsimp [c]
    linarith
  have hs := signed_slope_split_ge_neg_four_sq hc hq (by linarith) hE hA hA' ht
  have hdec := retained_child_decomposition
    (C := 1 - H ((1 - q) / 2)) hq hqd hE (by linarith) ht
  have hcEq : endpointCoefficient d = c + d / (2 * Real.log 2) := by
    dsimp [endpointCoefficient, c]
    ring
  rw [hcEq] at hdec
  have hsmall : 4 * q ^ 2 ≤ (1 / 100) * (q ^ 2 / E) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hE).2
    nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ 1 / 100 - 4 * E by linarith)]
  have hn : 0 ≤ q ^ 2 / E := by positivity
  nlinarith only [hgain, hr', hs, hdec, hsmall, hn]

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hside : 1 / 2 ≤ μ.b)
    (hEi : μ.meanEntropy ≤ 1 / 1000000)
    (hd4 : 4 * μ.meanEntropy ≤ μ.b - μ.a)
    (hd8 : μ.b - μ.a ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 20) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hq : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hqd : 1 - μ.a - μ.b ≤ μ.b - μ.a := by linarith
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hc := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
    (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
    (t := (μ.e - μ.f) / (μ.e + μ.f)) hq hqd (by rwa [hmean])
  have hca : (1 - (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.a := by ring
  have hcb : (1 + (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.b := by ring
  change μ.meanEntropy * (1 + (μ.e - μ.f) / (μ.e + μ.f)) = μ.e at hce
  change μ.meanEntropy * (1 - (μ.e - μ.f) / (μ.e + μ.f)) = μ.f at hcf
  rw [hca, hcb, hce, hcf] at hc
  change μ.gap ≤ _ at hc
  have h := retained_child_margin hE hEi hd4 hd8 hq hqd ht
  have hcost := PsiEndpointPlane.law_radial_lower μ (by linarith)
  linarith only [hc, h, hcost]

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hside : 1 / 2 ≤ μ.b)
    (hEi : μ.meanEntropy ≤ 1 / 1000000)
    (hd4 : 4 * μ.meanEntropy ≤ μ.b - μ.a)
    (hd8 : μ.b - μ.a ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm : 0 ≤ (1 / 20) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  have h := law_gap_margin μ hsum hside hEi hd4 hd8 hactive
  linarith only [h, hm]

end GeneralCK.PsiFourRatioBridge

#print axioms GeneralCK.PsiFourRatioBridge.radial_average_loss
#print axioms GeneralCK.PsiFourRatioBridge.retained_child_margin
#print axioms GeneralCK.PsiFourRatioBridge.law_gap_margin
#print axioms GeneralCK.PsiFourRatioBridge.law_gap_le_cost

end


