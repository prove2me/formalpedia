-- Prove2me | Definitions.Def_CK_GeneralCK_PsiModerateEntropy
-- name    : CK_GeneralCK_PsiModerateEntropy
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:01:35.613071+00:00
-- url     : https://prove2.me/theorems/1f532524-7c29-4847-bca8-bc14a7a04a53
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiModerateEntropy` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiModerateEntropy` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiModerateEntropy` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiModerateEntropy (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiModerateEntropy.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointBellman

-- ===== source module GeneralCK.PsiModerateEntropy =====
section

/-!
# Retained-child endpoint comparison up to average entropy 11/200

Keeping both bounds `q≤8E` and `q≤1/10` gives `q²≤4E/5`. This first proves
the range up to 1/32. A sharper upper-band parent estimate then reaches
11/200, the full currently proved child entropy-curvature range.
-/

namespace GeneralCK.PsiModerateEntropy
open PsiChildEntropyCoupling PsiSignedSplit

theorem parent_physical {E q : ℝ} (hE : 0 < E) (hEi : E ≤ 1 / 32)
    (hq : 0 ≤ q) (hqi : q ≤ 1 / 10) :
    E + (1 - H ((1 - q) / 2)) ≤ 1 := by
  rcases hq.eq_or_lt with he | hp
  · rw [← he]
    norm_num [H_half]
    linarith
  · have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
    have hsmall := mul_nonneg hq (show 0 ≤ 1 / 10 - q by linarith)
    nlinarith

theorem parent_gain {E q : ℝ} (hE : 0 < E) (hEi : E ≤ 1 / 32)
    (hq : 0 ≤ q) (hqi : q ≤ 1 / 10) (hqE : q ≤ 8 * E) :
    (50 / 77) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hgain := PsiLargerEntropyRedesign.parent_gain_rational hE hq (by linarith)
    (parent_physical hE hEi hq hqi)
  have hqSq : q ^ 2 ≤ (4 / 5) * E := by
    have hh := mul_le_mul_of_nonneg_right hqi hq
    nlinarith only [hh, hqE]
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have hh := Certificates.PilotData.log_two.2
    norm_num at hh
    linarith
  have hLsq : (Real.log 2) ^ 2 ≤ (49 / 100 : ℝ) := by nlinarith [log_two_pos]
  have hden : Real.log 2 * (2 * Real.log 2 * E + q ^ 2) ≤ (77 / 50) * E := by
    have h1 := mul_le_mul_of_nonneg_right hLsq hE.le
    have h2 := mul_le_mul hL hqSq (sq_nonneg q) (by norm_num : (0 : ℝ) ≤ 7 / 10)
    nlinarith only [h1, h2]
  have hb := div_le_div_of_nonneg_left (sq_nonneg q)
    (by positivity : 0 < Real.log 2 * (2 * Real.log 2 * E + q ^ 2)) hden
  have he : q ^ 2 / ((77 / 50) * E) = (50 / 77) * (q ^ 2 / E) := by ring
  rw [he] at hb
  exact hb.trans hgain

theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEi : E ≤ 1 / 32) (hd : 8 * E ≤ d) (hd1 : d ≤ 1)
    (hq : 0 ≤ q) (hqi : q ≤ 1 / 10) (hqE : q ≤ 8 * E) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 50) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
  have hqd : q ≤ d := hqE.trans hd
  have hg := parent_gain hE hEi hq hqi hqE
  have hr := PsiRadialDeficit.radial_average_loss_le_half hE hd q
  rw [abs_of_nonneg (show 0 ≤ d - q by linarith), abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
  have hr' : radialLoss d q E ≤ (q ^ 2 / E) / 2 := by
    rw [show q ^ 2 / (2 * E) = (q ^ 2 / E) / 2 by ring] at hr
    unfold radialLoss
    linarith only [hr]
  obtain ⟨hA, hA'⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq hqd
  have hc : 1 / 3 ≤ endpointCoefficient d := endpoint_coefficient_ge_third (by linarith) hd1
  have hs := PsiLargerEntropyRedesign.signed_split_ge_neg_four_sq hc hq hqi hE hA hA' ht
  have hdec := retained_child_decomposition (C := 1 - H ((1 - q) / 2)) hq hqd hE (by linarith) ht
  have hsmall : 4 * q ^ 2 ≤ (1 / 8) * (q ^ 2 / E) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hE).mpr
    nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ 1 / 8 - 4 * E by linarith)]
  have hnonneg : 0 ≤ q ^ 2 / E := by positivity
  linarith

theorem canonical_hybrid_gap_margin {d q E t : ℝ}
    (hE : 0 < E) (hEi : E ≤ 1 / 32) (hd : 8 * E ≤ d) (hd1 : d ≤ 1)
    (hq : 0 ≤ q) (hqi : q ≤ 1 / 10) (hqE : q ≤ 8 * E) (ht : |t| < 1)
    (hactive : phi ((1 - q) / 2) E ≤ psi ((1 - q) / 2) E) :
    candidateGap B ((1 - d - q) / 2) ((1 + d - q) / 2)
      (E * (1 + t)) (E * (1 - t)) + (1 / 50) * (q ^ 2 / E) ≤
      F d E + d / (2 * Real.log 2) * barrier t := by
  have h := retained_child_margin hE hEi hd hd1 hq hqi hqE ht
  have hb := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
    (t := t) hq (hqE.trans hd) hactive
  linarith

theorem law_gap_endpoint_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 32)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤
      F (μ.b - μ.a) μ.meanEntropy + (μ.b - μ.a) / (2 * Real.log 2) *
        barrier ((μ.e - μ.f) / (μ.e + μ.f)) := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hqeq : 1 - 2 * μ.midpoint = 1 - μ.a - μ.b := by
    unfold InteriorLaw.midpoint
    ring
  have hqE := PsiLargerEntropyLaw.active_bias_lt_eight_entropy hE (by rwa [hqeq]) hactive
  rw [hqeq] at hqE
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have h := canonical_hybrid_gap_margin
    (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
    (t := (μ.e - μ.f) / (μ.e + μ.f)) hE hEi hd
    (by linarith [μ.a_interior.1, μ.b_interior.2])
    (by linarith) hq hqE.le ht (by rwa [hmean])
  have hca : (1 - (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.a := by ring
  have hcb : (1 + (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.b := by ring
  change μ.meanEntropy * (1 + (μ.e - μ.f) / (μ.e + μ.f)) = μ.e at hce
  change μ.meanEntropy * (1 - (μ.e - μ.f) / (μ.e + μ.f)) = μ.f at hcf
  rwa [hca, hcb, hce, hcf] at h

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 32)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost :=
  (law_gap_endpoint_margin μ hsum hEi hd hq hactive).trans
    (PsiEndpointPlane.law_endpoint_logarithmic_lower μ hd)

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 32)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm : 0 ≤ (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  have hh := law_gap_margin μ hsum hEi hd hq hactive
  linarith only [hm, hh]

theorem parent_physical_ceiling {E q : ℝ} (hE : 0 < E) (hEi : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqi : q ≤ 1 / 10) :
    E + (1 - H ((1 - q) / 2)) ≤ 1 := by
  rcases hq.eq_or_lt with he | hp
  · rw [← he]
    norm_num [H_half]
    linarith
  · have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
    have hsmall := mul_nonneg hq (show 0 ≤ 1 / 10 - q by linarith)
    nlinarith

/-- Once E is above 1/32, its positive lower bound sharpens the rational
parent gain. This compensates for the larger absolute signed-split loss. -/
theorem parent_gain_upper_band {E q : ℝ} (hElo : 1 / 32 ≤ E) (hEi : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqi : q ≤ 1 / 10) :
    (250 / 301) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hE : 0 < E := by linarith
  have hgain := PsiLargerEntropyRedesign.parent_gain_rational hE hq (by linarith)
    (parent_physical_ceiling hE hEi hq hqi)
  have hqSq : q ^ 2 ≤ (8 / 25) * E := by
    have hh := mul_le_mul_of_nonneg_right hqi hq
    nlinarith only [hh, hqi, hElo]
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have hh := Certificates.PilotData.log_two.2
    norm_num at hh
    linarith
  have hLsq : (Real.log 2) ^ 2 ≤ (49 / 100 : ℝ) := by nlinarith [log_two_pos]
  have hden : Real.log 2 * (2 * Real.log 2 * E + q ^ 2) ≤ (301 / 250) * E := by
    have h1 := mul_le_mul_of_nonneg_right hLsq hE.le
    have h2 := mul_le_mul hL hqSq (sq_nonneg q) (by norm_num : (0 : ℝ) ≤ 7 / 10)
    nlinarith only [h1, h2]
  have hb := div_le_div_of_nonneg_left (sq_nonneg q)
    (by positivity : 0 < Real.log 2 * (2 * Real.log 2 * E + q ^ 2)) hden
  have he : q ^ 2 / ((301 / 250) * E) = (250 / 301) * (q ^ 2 / E) := by ring
  rw [he] at hb
  exact hb.trans hgain

/-- The complete currently proved entropy-curvature range is available. -/
theorem retained_child_margin_ceiling {d q E t : ℝ}
    (hE : 0 < E) (hEi : E ≤ 11 / 200) (hd : 8 * E ≤ d) (hd1 : d ≤ 1)
    (hq : 0 ≤ q) (hqi : q ≤ 1 / 10) (hqE : q ≤ 8 * E) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 50) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
  by_cases hElo : E ≤ 1 / 32
  · exact retained_child_margin hE hElo hd hd1 hq hqi hqE ht
  · have hqd : q ≤ d := hqE.trans hd
    have hg := parent_gain_upper_band (lt_of_not_ge hElo).le hEi hq hqi
    have hr := PsiRadialDeficit.radial_average_loss_le_half hE hd q
    rw [abs_of_nonneg (show 0 ≤ d - q by linarith), abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
    have hr' : radialLoss d q E ≤ (q ^ 2 / E) / 2 := by
      rw [show q ^ 2 / (2 * E) = (q ^ 2 / E) / 2 by ring] at hr
      unfold radialLoss
      linarith only [hr]
    obtain ⟨hA, hA'⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq hqd
    have hc : 1 / 3 ≤ endpointCoefficient d := endpoint_coefficient_ge_third (by linarith) hd1
    have hs := PsiLargerEntropyRedesign.signed_split_ge_neg_four_sq hc hq hqi hE hA hA' ht
    have hdec := retained_child_decomposition (C := 1 - H ((1 - q) / 2)) hq hqd hE hEi ht
    have hsmall : 4 * q ^ 2 ≤ (11 / 50) * (q ^ 2 / E) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hE).mpr
      nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ 11 / 50 - 4 * E by linarith)]
    have hnonneg : 0 ≤ q ^ 2 / E := by positivity
    linarith

theorem canonical_hybrid_gap_margin_ceiling {d q E t : ℝ}
    (hE : 0 < E) (hEi : E ≤ 11 / 200) (hd : 8 * E ≤ d) (hd1 : d ≤ 1)
    (hq : 0 ≤ q) (hqi : q ≤ 1 / 10) (hqE : q ≤ 8 * E) (ht : |t| < 1)
    (hactive : phi ((1 - q) / 2) E ≤ psi ((1 - q) / 2) E) :
    candidateGap B ((1 - d - q) / 2) ((1 + d - q) / 2)
      (E * (1 + t)) (E * (1 - t)) + (1 / 50) * (q ^ 2 / E) ≤
      F d E + d / (2 * Real.log 2) * barrier t := by
  have h := retained_child_margin_ceiling hE hEi hd hd1 hq hqi hqE ht
  have hb := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
    (t := t) hq (hqE.trans hd) hactive
  linarith

theorem law_gap_endpoint_margin_ceiling {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤
      F (μ.b - μ.a) μ.meanEntropy + (μ.b - μ.a) / (2 * Real.log 2) *
        barrier ((μ.e - μ.f) / (μ.e + μ.f)) := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hqeq : 1 - 2 * μ.midpoint = 1 - μ.a - μ.b := by
    unfold InteriorLaw.midpoint
    ring
  have hqE := PsiLargerEntropyLaw.active_bias_lt_eight_entropy hE (by rwa [hqeq]) hactive
  rw [hqeq] at hqE
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have h := canonical_hybrid_gap_margin_ceiling
    (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
    (t := (μ.e - μ.f) / (μ.e + μ.f)) hE hEi hd
    (by linarith [μ.a_interior.1, μ.b_interior.2])
    (by linarith) hq hqE.le ht (by rwa [hmean])
  have hca : (1 - (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.a := by ring
  have hcb : (1 + (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.b := by ring
  change μ.meanEntropy * (1 + (μ.e - μ.f) / (μ.e + μ.f)) = μ.e at hce
  change μ.meanEntropy * (1 - (μ.e - μ.f) / (μ.e + μ.f)) = μ.f at hcf
  rwa [hca, hcb, hce, hcf] at h

theorem law_gap_margin_ceiling {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost :=
  (law_gap_endpoint_margin_ceiling μ hsum hEi hd hq hactive).trans
    (PsiEndpointPlane.law_endpoint_logarithmic_lower μ hd)

theorem law_gap_le_cost_ceiling {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm : 0 ≤ (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  have hh := law_gap_margin_ceiling μ hsum hEi hd hq hactive
  linarith only [hm, hh]

end GeneralCK.PsiModerateEntropy

#print axioms GeneralCK.PsiModerateEntropy.parent_gain
#print axioms GeneralCK.PsiModerateEntropy.retained_child_margin
#print axioms GeneralCK.PsiModerateEntropy.law_gap_margin
#print axioms GeneralCK.PsiModerateEntropy.law_gap_le_cost
#print axioms GeneralCK.PsiModerateEntropy.parent_gain_upper_band
#print axioms GeneralCK.PsiModerateEntropy.retained_child_margin_ceiling
#print axioms GeneralCK.PsiModerateEntropy.law_gap_margin_ceiling
#print axioms GeneralCK.PsiModerateEntropy.law_gap_le_cost_ceiling

end


