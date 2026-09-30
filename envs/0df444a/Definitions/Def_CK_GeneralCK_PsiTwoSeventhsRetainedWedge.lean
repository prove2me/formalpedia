-- Prove2me | Definitions.Def_CK_GeneralCK_PsiTwoSeventhsRetainedWedge
-- name    : CK_GeneralCK_PsiTwoSeventhsRetainedWedge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:41:07.546816+00:00
-- url     : https://prove2.me/theorems/23f7846a-71a4-43c4-9ef2-841d8f79aa2e
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiTwoSeventhsRetainedWedge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiTwoSeventhsRetainedWedge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiTwoSeventhsRetainedWedge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiTwoSeventhsRetainedWedge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiTwoSeventhsRetainedWedge.lean)

import Definitions.Def_CK_GeneralCK_PsiFourFifteenthsParentClosure

-- ===== source module GeneralCK.PsiTwoSeventhsRetainedWedge =====
section

/-! Actual retained-child closure through bias two sevenths, with an explicit ratio-eight premise. -/

namespace GeneralCK.PsiTwoSeventhsRetainedWedge
open Set PsiChildEntropyCoupling PsiSignedSplit

theorem endpoint_coefficient {d q : ℝ} (hd : 0 ≤ d)
    (hq : 1 / 4 ≤ q) (hphysical : d + q ≤ 1) :
    4 / 9 ≤ endpointCoefficient d := by
  have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hm := mul_le_mul_of_nonneg_left hL (by linarith : 0 ≤ 1 + d)
  have hf : 18 * (1 + d) / 25 ≤ (1 + d) / (2 * Real.log 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).mpr
    nlinarith
  unfold endpointCoefficient
  linarith

theorem capacity_quadratic_seven_tenths {z : ℝ}
    (hz : 0 ≤ z) (hzu : z ≤ 7 / 10) : capacity z ≤ (355 / 612) * z ^ 2 := by
  have hz1 : z < 1 := by linarith
  rw [capacity_eq_Cn (by rw [abs_of_nonneg hz]; exact hz1)]
  have hs : z ^ 2 ≤ 49 / 100 := by nlinarith
  have hn : 0 < 1 - z ^ 2 := by linarith
  have hf : z ^ 2 / (12 * (1 - z ^ 2)) ≤ (49 / 612 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - z ^ 2))).mpr
    nlinarith only [hs]
  have h := LowInformation.Cn_upper_sharp hz hz1
  have hh := mul_le_mul_of_nonneg_left hf (sq_nonneg z)
  have he : z ^ 2 * (z ^ 2 / (12 * (1 - z ^ 2))) = z ^ 4 / (12 * (1 - z ^ 2)) := by ring
  rw [he] at hh
  linarith

theorem split_loss {c q : ℝ} (hc : 4 / 9 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 2 / 7) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ (59995 / 19584) * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (4 / 9 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (4 / 9 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  rw [show (13 * q / 6) / (2 * (4 / 9 : ℝ)) = 39 * q / 16 by ring] at h
  have hb := capacity_quadratic_seven_tenths (z := 39 * q / 16) (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

theorem log_one_twenty_nine_forty_ninths : (24 / 25 : ℝ) ≤ Real.log (129 / 49) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 40 / 89)
    (by norm_num : (40 / 89 : ℝ) < 1) 3
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

theorem logarithmic_chord {R : ℝ} (hR : 0 ≤ R) (hRu : R ≤ 16 / 7) :
    (3 / 5) * R ≤ Real.log (1 + (5 / 7) * R) / Real.log 2 := by
  have hs := strictConcaveOn_log_Ioi.concaveOn.2
    (show (129 / 49 : ℝ) ∈ Ioi 0 by norm_num) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show 0 ≤ (7 / 16) * R by positivity) (show 0 ≤ 1 - (7 / 16) * R by linarith)
    (show (7 / 16) * R + (1 - (7 / 16) * R) = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hs
  have he : (7 / 16) * R * (129 / 49) + (1 - (7 / 16) * R) * 1 = 1 + (5 / 7) * R := by ring
  rw [he] at hs
  have hl := mul_le_mul_of_nonneg_left log_one_twenty_nine_forty_ninths
    (show 0 ≤ (7 / 16) * R by positivity)
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hm := mul_le_mul_of_nonneg_right hL hR
  apply (le_div_iff₀ log_two_pos).mpr
  nlinarith only [hs, hl, hm]

theorem parent_gain {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 2 / 7) (hqE : q ≤ 8 * E) :
    (3 / 5 + (10 / 7) * E) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  let C := 1 - H ((1 - q) / 2)
  let R := q ^ 2 / E
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRu : R ≤ 16 / 7 := by
    apply (div_le_iff₀ hE).mpr
    nlinarith only [mul_nonneg hq (show 0 ≤ 2 / 7 - q by linarith), hqE]
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hClower := SmallMean.Cn_ge_half_sq hq (show q ≤ 1 by linarith)
  change q ^ 2 / 2 ≤ Real.log 2 * C at hClower
  have hClow : (5 / 7) * q ^ 2 ≤ C := by
    have hm := mul_le_mul_of_nonneg_right hL hC
    nlinarith only [hm, hClower]
  have harg : (5 / 7) * R ≤ C / E := by
    have hm := div_le_div_of_nonneg_right hClow hE.le
    convert! hm using 1 <;> dsimp [R] <;> ring
  have hphys : E + C ≤ 1 := by
    have hh := PsiFourFifteenthsParent.parent_capacity_upper hq hqu
    change C ≤ (37 / 50) * q ^ 2 at hh
    have hs : q ^ 2 ≤ 4 / 49 := by nlinarith
    linarith only [hh, hs, hEu]
  have hg := eta_increment_ge_linear_log hE hC hphys
  have hl := logarithmic_chord hR hRu
  have hm : Real.log (1 + (5 / 7) * R) ≤ Real.log (1 + C / E) :=
    Real.log_le_log (by positivity) (by linarith only [harg])
  have hlog := div_le_div_of_nonneg_right hm log_two_pos.le
  have hER : E * R = q ^ 2 := by dsimp [R]; field_simp
  change (3 / 5 + (10 / 7) * E) * R ≤ eta E - eta (E + C)
  nlinarith only [hl, hlog, hg, hClow, hER]

theorem parent_gain_budget {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 2 / 7) (hqE : q ≤ 8 * E) :
    (1 / 2 + (59995 / 19584) * E + 1 / 100) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hg := parent_gain hE hEu hq hqu hqE
  have hm := mul_le_mul_of_nonneg_right
    (show 1 / 2 + (59995 / 19584) * E + 1 / 100 ≤ 3 / 5 + (10 / 7) * E by linarith)
    (show 0 ≤ q ^ 2 / E by positivity)
  exact hm.trans hg

theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEu : E ≤ 11 / 200) (hd : 8 * E ≤ d)
    (hq : 1 / 4 ≤ q) (hqu : q ≤ 2 / 7) (hqE : q ≤ 8 * E)
    (hphysical : d + q ≤ 1) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 100) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
  let K : ℝ := 59995 / 19584
  have hq0 : 0 ≤ q := by linarith
  have hqd : q ≤ d := hqE.trans hd
  have hK : 0 ≤ K := by norm_num [K]
  have hc := endpoint_coefficient (by linarith : 0 ≤ d) hq hphysical
  have hk : |13 * q / 6| < 2 * endpointCoefficient d := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have hloss : 2 * endpointCoefficient d * capacity ((13 * q / 6) / (2 * endpointCoefficient d)) ≤ K * q ^ 2 := by
    exact split_loss hc hq0 hqu
  have hg := parent_gain_budget hE hEu hq0 hqu hqE
  change (1 / 2 + K * E + 1 / 100) * (q ^ 2 / E) ≤ _ at hg
  have hr := PsiRadialDeficit.radial_average_loss_le_half hE hd q
  rw [abs_of_nonneg (show 0 ≤ d - q by linarith),
    abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
  have hr' : radialLoss d q E ≤ (q ^ 2 / E) / 2 := by
    rw [show q ^ 2 / (2 * E) = (q ^ 2 / E) / 2 by ring] at hr
    unfold radialLoss
    linarith only [hr]
  obtain ⟨hA, hAu⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq0 hqd
  have hs := PsiQuarterBias.signed_split_of_loss (by linarith : 0 < endpointCoefficient d)
    hq0 hK hk hloss hE hA hAu ht
  have hdec := retained_child_decomposition (C := 1 - H ((1 - q) / 2)) hq0 hqd hE hEu ht
  have he : (1 / 2 + K * E + 1 / 100) * (q ^ 2 / E) =
      (1 / 2 + 1 / 100) * (q ^ 2 / E) + K * q ^ 2 := by
    field_simp
    ring
  rw [he] at hg
  linarith only [hg, hr', hs, hdec]

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEu : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 2 / 7)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_cases hfifth : 1 - μ.a - μ.b ≤ 1 / 4
  · exact PsiQuarterBias.law_gap_margin μ hsum hEu hd hfifth hactive
  · obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
    have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
      unfold InteriorLaw.midpoint
      ring
    have hm := retained_child_margin (d := μ.b - μ.a) (q := 1 - μ.a - μ.b)
      (E := μ.meanEntropy) (t := (μ.e - μ.f) / (μ.e + μ.f)) hE hEu hd
      (lt_of_not_ge hfifth).le hq hqE (by linarith [μ.a_interior.1]) ht
    have hb := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
      (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
      (t := (μ.e - μ.f) / (μ.e + μ.f)) (by linarith) (hqE.trans hd) (by rwa [hmean])
    have hca : (1 - (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.a := by ring
    have hcb : (1 + (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.b := by ring
    change μ.meanEntropy * (1 + (μ.e - μ.f) / (μ.e + μ.f)) = μ.e at hce
    change μ.meanEntropy * (1 - (μ.e - μ.f) / (μ.e + μ.f)) = μ.f at hcf
    rw [hca, hcb, hce, hcf, hmean] at hb
    rw [hmean] at hm
    have hcost := PsiEndpointPlane.law_endpoint_logarithmic_lower μ hd
    change μ.gap ≤ eta (μ.meanEntropy + (1 - H μ.midpoint)) -
      childAverage (μ.b - μ.a) (1 - μ.a - μ.b) μ.meanEntropy
        ((μ.e - μ.f) / (μ.e + μ.f)) at hb
    linarith only [hm, hb, hcost]

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEu : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 2 / 7)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hh := law_gap_margin μ hsum hEu hd hq hqE hactive
  have hn : 0 ≤ (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [hh, hn]

end GeneralCK.PsiTwoSeventhsRetainedWedge

#print axioms GeneralCK.PsiTwoSeventhsRetainedWedge.endpoint_coefficient
#print axioms GeneralCK.PsiTwoSeventhsRetainedWedge.capacity_quadratic_seven_tenths
#print axioms GeneralCK.PsiTwoSeventhsRetainedWedge.split_loss
#print axioms GeneralCK.PsiTwoSeventhsRetainedWedge.log_one_twenty_nine_forty_ninths
#print axioms GeneralCK.PsiTwoSeventhsRetainedWedge.logarithmic_chord
#print axioms GeneralCK.PsiTwoSeventhsRetainedWedge.parent_gain
#print axioms GeneralCK.PsiTwoSeventhsRetainedWedge.parent_gain_budget
#print axioms GeneralCK.PsiTwoSeventhsRetainedWedge.retained_child_margin
#print axioms GeneralCK.PsiTwoSeventhsRetainedWedge.law_gap_margin
#print axioms GeneralCK.PsiTwoSeventhsRetainedWedge.law_gap_le_cost

end


