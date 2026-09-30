-- Prove2me | Definitions.Def_CK_GeneralCK_PsiCentralTwentyFourWedge
-- name    : CK_GeneralCK_PsiCentralTwentyFourWedge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:44:15.998519+00:00
-- url     : https://prove2.me/theorems/d3b2e178-65eb-4f74-ab69-02eeaf3cfc3f
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiCentralTwentyFourWedge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiCentralTwentyFourWedge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiCentralTwentyFourWedge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiCentralTwentyFourWedge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiCentralTwentyFourWedge.lean)

import Definitions.Def_CK_GeneralCK_PsiCentralSixteenWedge

-- ===== source module GeneralCK.PsiCentralTwentyFourWedge =====
section

/-!
# A retained-child central wedge at separation ratio twenty-four

The improved radial loss at ratio twenty-four closes a central medium-bias
region left by the ratio-28 parent exclusion. Both child profiles and the
entire entropy allocation are retained throughout the proof.
-/

namespace GeneralCK.PsiCentralTwentyFourWedge

open Set PsiChildEntropyCoupling PsiSignedSplit
open Certificates.Mixed Certificates.Mixed.Tails

theorem contact_twenty_four_bracket :
    (1 : ℝ) / 256 ≤ radialContact 24 1 ∧ radialContact 24 1 ≤ 1 / 65 := by
  have hlog : Real.log ((1 / 256 : ℝ)⁻¹) ≤ 8 * Real.log 2 := by
    norm_num
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hH := (PsiOuterEntropy2048.entropy_logit_upper
    (p := (1 / 256 : ℝ)) (n := 8) (by norm_num) (by norm_num) hlog).1
  constructor
  · apply (le_radialContact_iff (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).mpr
    norm_num at hH ⊢
    linarith
  · exact PsiParentContactEnvelope.contact_le_one_div_65
      (by norm_num) (by norm_num) (by norm_num)

theorem radial_ratio_le_five_twenty_fourths {x : ℝ} (hx : 24 ≤ x) :
    deriv (fun r => F r 1) x / (2 * x) ≤ 5 / 24 := by
  have hm := antitoneOn_F_radius_ratio (by norm_num : (0 : ℝ) < 1)
    (show (24 : ℝ) ∈ Ioi 0 by norm_num)
    (show x ∈ Ioi 0 by change 0 < x; linarith) hx
  have hd : deriv (fun r => F r 1) 24 < 10 := by
    rw [deriv_F_radius_slope (by norm_num) (by norm_num)]
    exact PsiCentralSixteenWedge.radial_slope_lt_ten contact_twenty_four_bracket.1 contact_twenty_four_bracket.2
  exact hm.trans (by norm_num; linarith)

theorem radial_average_loss {d E : ℝ}
    (hE : 0 < E) (hd : 24 * E ≤ d) (q : ℝ) :
    (F |d - q| E + F |d + q| E) / 2 - F d E ≤ (5 / 24) * (q ^ 2 / E) := by
  have hd0 : 0 < d := by linarith
  have hx : 24 ≤ d / E := (le_div_iff₀ hE).mpr hd
  have hb := radial_ratio_le_five_twenty_fourths hx
  have hh := F_average_difference_le hd0 hE q
  have heq : q ^ 2 / (2 * d) * deriv (fun r => F r E) d =
      (q ^ 2 / E) * (deriv (fun r => F r 1) (d / E) / (2 * (d / E))) := by
    rw [deriv_F_radius_normalize hd0 hE]
    field_simp
  have hp := mul_le_mul_of_nonneg_left hb (show 0 ≤ q ^ 2 / E by positivity)
  rw [heq] at hh
  nlinarith only [hh, hp]

theorem endpoint_coefficient {d : ℝ} (hd : 0 ≤ d) (hdu : d ≤ 1 / 2) :
    8 / 15 ≤ endpointCoefficient d := by
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

theorem split_loss {c q : ℝ} (hc : 8 / 15 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 7 / 20) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ 3 * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (8 / 15 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (8 / 15 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  rw [show (13 * q / 6) / (2 * (8 / 15 : ℝ)) = 65 * q / 32 by ring] at h
  have hb := PsiThreeTenthsRetainedWedge.capacity_quadratic_five_sevenths
    (z := 65 * q / 32) (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

theorem log_sixty_seven_sevenths : (9 / 4 : ℝ) ≤ Real.log (67 / 7) := by
  have hL : (693 / 1000 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 56)
  norm_num at h
  have he : Real.log (67 / 7 : ℝ) = 3 * Real.log 2 + Real.log (67 / 56) := by
    rw [show (67 / 7 : ℝ) = 2 ^ (3 : ℕ) * (67 / 56) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  linarith

theorem logarithmic_chord {R : ℝ} (hR : 0 ≤ R) (hRu : R ≤ 12) :
    (4 / 15) * R ≤ Real.log (1 + (5 / 7) * R) / Real.log 2 := by
  have hs := strictConcaveOn_log_Ioi.concaveOn.2
    (show (67 / 7 : ℝ) ∈ Ioi 0 by norm_num) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show 0 ≤ (1 / 12) * R by positivity) (show 0 ≤ 1 - (1 / 12) * R by linarith)
    (show (1 / 12) * R + (1 - (1 / 12) * R) = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hs
  have he : (1 / 12) * R * (67 / 7) + (1 - (1 / 12) * R) * 1 =
      1 + (5 / 7) * R := by ring
  rw [he] at hs
  have hl := mul_le_mul_of_nonneg_left log_sixty_seven_sevenths
    (show 0 ≤ (1 / 12) * R by positivity)
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hm := mul_le_mul_of_nonneg_right hL hR
  apply (le_div_iff₀ log_two_pos).mpr
  nlinarith only [hs, hl, hm, hR]

theorem parent_gain {E q : ℝ} (hEl : 3 / 280 ≤ E) (hEu : E ≤ 1 / 48)
    (hq : 0 ≤ q) (hqu : q ≤ 7 / 20) :
    (4 / 15 + (10 / 7) * E) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hE : 0 < E := by linarith
  let C := 1 - H ((1 - q) / 2)
  let R := q ^ 2 / E
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRu : R ≤ 12 := by
    apply (div_le_iff₀ hE).mpr
    nlinarith only [mul_nonneg hq (show 0 ≤ 7 / 20 - q by linarith), hqu, hEl]
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
    have hh := PsiParentPhiFloor.entropy_chord
      (show 0 ≤ (1 - q) / 2 by linarith) (show (1 - q) / 2 ≤ 1 / 2 by linarith)
    dsimp [C]
    linarith
  have hg := eta_increment_ge_linear_log hE hC hphys
  have hl := logarithmic_chord hR hRu
  have hm : Real.log (1 + (5 / 7) * R) ≤ Real.log (1 + C / E) :=
    Real.log_le_log (by positivity) (by linarith only [harg])
  have hlog := div_le_div_of_nonneg_right hm log_two_pos.le
  have hER : E * R = q ^ 2 := by dsimp [R]; field_simp
  change (4 / 15 + (10 / 7) * E) * R ≤ eta E - eta (E + C)
  nlinarith only [hl, hlog, hg, hClow, hER]

theorem retained_child_margin {d q E t : ℝ}
    (hEl : 3 / 280 ≤ E) (hEu : E ≤ 1 / 48)
    (hd : 24 * E ≤ d) (hdu : d ≤ 1 / 2)
    (hq : 0 ≤ q) (hqu : q ≤ 7 / 20) (hqd : q ≤ d) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 50) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
  have hE : 0 < E := by linarith
  have hc := endpoint_coefficient (by linarith : 0 ≤ d) hdu
  have hk : |13 * q / 6| < 2 * endpointCoefficient d := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have hloss := split_loss hc hq hqu
  have hg := parent_gain hEl hEu hq hqu
  have hr := radial_average_loss hE hd q
  rw [abs_of_nonneg (show 0 ≤ d - q by linarith),
    abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
  have hr' : radialLoss d q E ≤ (5 / 24) * (q ^ 2 / E) := by
    unfold radialLoss
    linarith only [hr]
  obtain ⟨hA, hAu⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq hqd
  have hs := PsiQuarterBias.signed_split_of_loss (by linarith : 0 < endpointCoefficient d)
    hq (by norm_num : (0 : ℝ) ≤ 3) hk hloss hE hA hAu ht
  have hdec := retained_child_decomposition (C := 1 - H ((1 - q) / 2))
    hq hqd hE (by linarith) ht
  have hbudget : (5 / 24 + 3 * E + 1 / 50) * (q ^ 2 / E) ≤
      (4 / 15 + (10 / 7) * E) * (q ^ 2 / E) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have he : (5 / 24 + 3 * E + 1 / 50) * (q ^ 2 / E) =
      (5 / 24 + 1 / 50) * (q ^ 2 / E) + 3 * q ^ 2 := by
    field_simp
    ring
  rw [he] at hbudget
  linarith only [hg, hbudget, hr', hs, hdec]

/-- Actual-law closure retains both children and all feasible entropy splits. -/
theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hb : 1 / 2 ≤ μ.b)
    (hEl : 3 / 280 ≤ μ.meanEntropy) (hEu : μ.meanEntropy ≤ 1 / 48)
    (hd : 24 * μ.meanEntropy ≤ μ.b - μ.a) (hdu : μ.b - μ.a ≤ 1 / 2)
    (hq : 1 - μ.a - μ.b ≤ 7 / 20)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by linarith
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hqd : 1 - μ.a - μ.b ≤ μ.b - μ.a := by linarith
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hm := retained_child_margin (d := μ.b - μ.a) (q := 1 - μ.a - μ.b)
    (E := μ.meanEntropy) (t := (μ.e - μ.f) / (μ.e + μ.f))
    hEl hEu hd hdu hq0 hq hqd ht
  have hchild := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
    (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
    (t := (μ.e - μ.f) / (μ.e + μ.f)) hq0 hqd (by rwa [hmean])
  have hca : (1 - (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.a := by ring
  have hcb : (1 + (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.b := by ring
  change μ.meanEntropy * (1 + (μ.e - μ.f) / (μ.e + μ.f)) = μ.e at hce
  change μ.meanEntropy * (1 - (μ.e - μ.f) / (μ.e + μ.f)) = μ.f at hcf
  rw [hca, hcb, hce, hcf, hmean] at hchild
  rw [hmean] at hm
  have hcost := PsiEndpointPlane.law_endpoint_logarithmic_lower μ (by linarith)
  change μ.gap ≤ eta (μ.meanEntropy + (1 - H μ.midpoint)) -
    childAverage (μ.b - μ.a) (1 - μ.a - μ.b) μ.meanEntropy
      ((μ.e - μ.f) / (μ.e + μ.f)) at hchild
  linarith only [hm, hchild, hcost]

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hb : 1 / 2 ≤ μ.b)
    (hEl : 3 / 280 ≤ μ.meanEntropy) (hEu : μ.meanEntropy ≤ 1 / 48)
    (hd : 24 * μ.meanEntropy ≤ μ.b - μ.a) (hdu : μ.b - μ.a ≤ 1 / 2)
    (hq : 1 - μ.a - μ.b ≤ 7 / 20)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by linarith
  have hm := law_gap_margin μ hsum hb hEl hEu hd hdu hq hactive
  have hn : 0 ≤ (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [hm, hn]

/-- Exact complement of the new wedge within the previously narrowed owner.
The ratio-28 clipping already supplies the required lower entropy bound. -/
def centralRegion (a b E : ℝ) : Prop :=
  PsiCentralSixteenWedge.centralRegion a b E ∧
    (1 - a - b < 3 / 10 ∨ 7 / 20 < 1 - a - b ∨ b - a < 24 * E)

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
    centralRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toSixteenCentralOwner (h : CentralOwner) : PsiCentralSixteenWedge.CentralOwner := by
  intro k μ hab hregion hactive
  by_cases hw : 3 / 10 ≤ 1 - μ.a - μ.b ∧ 1 - μ.a - μ.b ≤ 7 / 20 ∧
      24 * μ.meanEntropy ≤ μ.b - μ.a
  · have h28 : PsiThreeTenthsTail28.centralRegion μ.a μ.b μ.meanEntropy := hregion.1
    have hbase : PsiCentralAnalytic.centralRegion μ.a μ.b μ.meanEntropy :=
      h28.1.1.1.1.1.1.1.1.1.1
    have hdu : μ.b - μ.a ≤ 1 / 2 := by linarith [hbase.2.2.1, hw.1]
    have hEl : 3 / 280 ≤ μ.meanEntropy := by linarith [h28.2, hw.1]
    have hEu : μ.meanEntropy ≤ 1 / 48 := by linarith [hw.2.2]
    exact law_gap_le_cost μ hbase.1.le hbase.2.1 hEl hEu hw.2.2 hdu hw.2.1 hactive.le
  · apply h k μ hab ⟨hregion, ?_⟩ hactive
    by_contra hn
    push Not at hn
    exact hw hn

#print axioms contact_twenty_four_bracket
#print axioms radial_ratio_le_five_twenty_fourths
#print axioms radial_average_loss
#print axioms endpoint_coefficient
#print axioms split_loss
#print axioms log_sixty_seven_sevenths
#print axioms logarithmic_chord
#print axioms parent_gain
#print axioms retained_child_margin
#print axioms law_gap_margin
#print axioms law_gap_le_cost
#print axioms toSixteenCentralOwner

end GeneralCK.PsiCentralTwentyFourWedge

end


