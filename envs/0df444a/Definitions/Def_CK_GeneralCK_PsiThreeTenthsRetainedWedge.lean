-- Prove2me | Definitions.Def_CK_GeneralCK_PsiThreeTenthsRetainedWedge
-- name    : CK_GeneralCK_PsiThreeTenthsRetainedWedge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:04:10.701033+00:00
-- url     : https://prove2.me/theorems/57390290-2705-475f-b171-ce7e4fd6f2eb
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiThreeTenthsRetainedWedge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiThreeTenthsRetainedWedge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiThreeTenthsRetainedWedge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiThreeTenthsRetainedWedge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiThreeTenthsRetainedWedge.lean)

import Definitions.Def_CK_GeneralCK_PsiThreeTenthsParentClosure

-- ===== source module GeneralCK.PsiThreeTenthsRetainedWedge =====
section

/-! Actual retained-child closure through bias three tenths, with an explicit ratio-eight premise. -/

namespace GeneralCK.PsiThreeTenthsRetainedWedge
open Set PsiChildEntropyCoupling PsiSignedSplit

theorem endpoint_coefficient {d q : ℝ} (hd : 0 ≤ d)
    (hq : 2 / 7 ≤ q) (hphysical : d + q ≤ 1) :
    23 / 50 ≤ endpointCoefficient d := by
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

theorem capacity_quadratic_five_sevenths {z : ℝ}
    (hz : 0 ≤ z) (hzu : z ≤ 5 / 7) : capacity z ≤ (169 / 288) * z ^ 2 := by
  have hz1 : z < 1 := by linarith
  rw [capacity_eq_Cn (by rw [abs_of_nonneg hz]; exact hz1)]
  have hs : z ^ 2 ≤ 25 / 49 := by nlinarith
  have hn : 0 < 1 - z ^ 2 := by linarith
  have hf : z ^ 2 / (12 * (1 - z ^ 2)) ≤ (25 / 288 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - z ^ 2))).mpr
    nlinarith only [hs]
  have h := LowInformation.Cn_upper_sharp hz hz1
  have hh := mul_le_mul_of_nonneg_left hf (sq_nonneg z)
  have he : z ^ 2 * (z ^ 2 / (12 * (1 - z ^ 2))) = z ^ 4 / (12 * (1 - z ^ 2)) := by ring
  rw [he] at hh
  linarith

theorem split_loss {c q : ℝ} (hc : 23 / 50 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 3 / 10) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ (714025 / 238464) * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (23 / 50 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (23 / 50 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  rw [show (13 * q / 6) / (2 * (23 / 50 : ℝ)) = 325 * q / 138 by ring] at h
  have hb := capacity_quadratic_five_sevenths (z := 325 * q / 138) (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

theorem log_nineteen_sevenths : (4991 / 5000 : ℝ) ≤ Real.log (19 / 7) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 6 / 13)
    (by norm_num : (6 / 13 : ℝ) < 1) 4
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

theorem logarithmic_chord {R : ℝ} (hR : 0 ≤ R) (hRu : R ≤ 12 / 5) :
    (3 / 5) * R ≤ Real.log (1 + (5 / 7) * R) / Real.log 2 := by
  have hs := strictConcaveOn_log_Ioi.concaveOn.2
    (show (19 / 7 : ℝ) ∈ Ioi 0 by norm_num) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show 0 ≤ (5 / 12) * R by positivity) (show 0 ≤ 1 - (5 / 12) * R by linarith)
    (show (5 / 12) * R + (1 - (5 / 12) * R) = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hs
  have he : (5 / 12) * R * (19 / 7) + (1 - (5 / 12) * R) * 1 = 1 + (5 / 7) * R := by ring
  rw [he] at hs
  have hl := mul_le_mul_of_nonneg_left log_nineteen_sevenths
    (show 0 ≤ (5 / 12) * R by positivity)
  have hL : Real.log 2 ≤ (69315 / 100000 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hm := mul_le_mul_of_nonneg_right hL hR
  apply (le_div_iff₀ log_two_pos).mpr
  nlinarith only [hs, hl, hm, hR]

theorem parent_gain {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 3 / 10) (hqE : q ≤ 8 * E) :
    (3 / 5 + (10 / 7) * E) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  let C := 1 - H ((1 - q) / 2)
  let R := q ^ 2 / E
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRu : R ≤ 12 / 5 := by
    apply (div_le_iff₀ hE).mpr
    nlinarith only [mul_nonneg hq (show 0 ≤ 3 / 10 - q by linarith), hqE]
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
    have hh := PsiThreeTenthsParent.parent_capacity_upper hq hqu
    change C ≤ (37 / 50) * q ^ 2 at hh
    have hs : q ^ 2 ≤ 9 / 100 := by nlinarith
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
    (hq : 0 ≤ q) (hqu : q ≤ 3 / 10) (hqE : q ≤ 8 * E) :
    (1 / 2 + (714025 / 238464) * E + 1 / 100) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hg := parent_gain hE hEu hq hqu hqE
  have hm := mul_le_mul_of_nonneg_right
    (show 1 / 2 + (714025 / 238464) * E + 1 / 100 ≤ 3 / 5 + (10 / 7) * E by linarith)
    (show 0 ≤ q ^ 2 / E by positivity)
  exact hm.trans hg

theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEu : E ≤ 11 / 200) (hd : 8 * E ≤ d)
    (hq : 2 / 7 ≤ q) (hqu : q ≤ 3 / 10) (hqE : q ≤ 8 * E)
    (hphysical : d + q ≤ 1) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 100) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
  let K : ℝ := 714025 / 238464
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
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 3 / 10)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_cases hfifth : 1 - μ.a - μ.b ≤ 2 / 7
  · exact PsiTwoSeventhsBias.law_gap_margin μ hsum hEu hd hfifth hactive
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
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 3 / 10)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hh := law_gap_margin μ hsum hEu hd hq hqE hactive
  have hn : 0 ≤ (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [hh, hn]

end GeneralCK.PsiThreeTenthsRetainedWedge

#print axioms GeneralCK.PsiThreeTenthsRetainedWedge.endpoint_coefficient
#print axioms GeneralCK.PsiThreeTenthsRetainedWedge.capacity_quadratic_five_sevenths
#print axioms GeneralCK.PsiThreeTenthsRetainedWedge.split_loss
#print axioms GeneralCK.PsiThreeTenthsRetainedWedge.log_nineteen_sevenths
#print axioms GeneralCK.PsiThreeTenthsRetainedWedge.logarithmic_chord
#print axioms GeneralCK.PsiThreeTenthsRetainedWedge.parent_gain
#print axioms GeneralCK.PsiThreeTenthsRetainedWedge.parent_gain_budget
#print axioms GeneralCK.PsiThreeTenthsRetainedWedge.retained_child_margin
#print axioms GeneralCK.PsiThreeTenthsRetainedWedge.law_gap_margin
#print axioms GeneralCK.PsiThreeTenthsRetainedWedge.law_gap_le_cost

end


