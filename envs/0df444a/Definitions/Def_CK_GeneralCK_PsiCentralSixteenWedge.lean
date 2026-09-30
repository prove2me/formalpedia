-- Prove2me | Definitions.Def_CK_GeneralCK_PsiCentralSixteenWedge
-- name    : CK_GeneralCK_PsiCentralSixteenWedge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:38:30.508986+00:00
-- url     : https://prove2.me/theorems/cde0c2c3-b797-4184-bc4f-a83cfcd55c85
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiCentralSixteenWedge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiCentralSixteenWedge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiCentralSixteenWedge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiCentralSixteenWedge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiCentralSixteenWedge.lean)

import Definitions.Def_CK_GeneralCK_PsiThreeTenthsTail28

-- ===== source module GeneralCK.PsiCentralSixteenWedge =====
section

/-!
# A retained-child central wedge at separation ratio sixteen

The improved radial loss at ratio sixteen closes a central medium-bias
region left by the ratio-28 parent exclusion. Both child profiles and the
entire entropy allocation are retained throughout the proof.
-/

namespace GeneralCK.PsiCentralSixteenWedge

open Set PsiChildEntropyCoupling PsiSignedSplit
open Certificates.Mixed Certificates.Mixed.Tails

theorem contact_sixteen_bracket :
    (1 : ℝ) / 256 ≤ radialContact 16 1 ∧ radialContact 16 1 ≤ 1 / 65 := by
  have hv : 0 < radialContact 16 1 := radialContact_pos (by norm_num) (by norm_num)
  have hh := PsiParentContactEnvelope.contact_odds_polynomial
    (q := 16) (E := 1) (n := 5) (r := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; norm_num)
    (by norm_num)
  norm_num at hh
  have hp := (div_le_iff₀ hv).mp hh
  exact ⟨by linarith,
    PsiParentContactEnvelope.contact_le_one_div_65 (by norm_num) (by norm_num) (by norm_num)⟩

theorem radial_slope_lt_ten {v : ℝ}
    (hl : 1 / 256 ≤ v) (hu : v ≤ 1 / 65) : radialSlope v < 10 := by
  have hv : 0 < v := by linarith
  have hvh : v < 1 / 2 := by linarith
  have hL : 0 < Real.log 2 := log_two_pos
  have hk := kap_pos hv hvh
  have hc : 0 < 1 - v := by linarith
  have hh0 : 0 ≤ hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_nonneg (H_nonneg hv.le (by linarith)) hL.le
  have hJ : J v < 8 := by
    have hm := J_antitone (by norm_num : (0 : ℝ) < 1 / 256) hvh.le hl
    have ha : J (1 / 256 : ℝ) < 8 := by
      have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 255)
        (by norm_num : (255 : ℝ) < 256)
      rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow] at h
      unfold J
      norm_num
      apply (div_lt_iff₀ hL).mpr
      simpa using h
    exact hm.trans_lt ha
  have he : (69 / 20 : ℝ) ≤ logit v := by
    have hr : (32 : ℝ) ≤ (1 - v) / v := (le_div_iff₀ hv).mpr (by linarith)
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 32) hr
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow] at hm
    unfold logit
    nlinarith [log_two_gt_69]
  have he0 : 0 < logit v := by linarith
  have hratio := left_ratio_bound hv (show v ≤ 1 / 22 by linarith)
  have hratio' : hn v / ((4 * v * (1 - v)) * kap v) ≤
      (10 / 19 : ℝ) * (1 + (20 / 19) / (69 / 20)) := by
    apply hratio.trans
    gcongr
  have hratio0 : 0 ≤ hn v / ((4 * v * (1 - v)) * kap v) := by positivity
  have hcoef : 2 * (1 - 2 * v) / Real.log 2 ≤ (200 / 69 : ℝ) := by
    apply (div_le_iff₀ hL).mpr
    nlinarith [log_two_gt_69]
  have hh := mul_le_mul hcoef hratio' hratio0 (by norm_num : (0 : ℝ) ≤ 200 / 69)
  have hid : (2 * (1 - 2 * v) / Real.log 2) *
      (hn v / ((4 * v * (1 - v)) * kap v)) =
      (1 - 2 * v) * hn v / (2 * Real.log 2 * v * (1 - v) * kap v) := by
    field_simp
    ring
  rw [hid] at hh
  have hcorrection : (1 - 2 * v) * hn v /
      (2 * Real.log 2 * v * (1 - v) * kap v) < 2 := hh.trans_lt (by norm_num)
  unfold radialSlope
  linarith

theorem radial_ratio_le_five_sixteenths {x : ℝ} (hx : 16 ≤ x) :
    deriv (fun r => F r 1) x / (2 * x) ≤ 5 / 16 := by
  have hm := antitoneOn_F_radius_ratio (by norm_num : (0 : ℝ) < 1)
    (show (16 : ℝ) ∈ Ioi 0 by norm_num)
    (show x ∈ Ioi 0 by change 0 < x; linarith) hx
  have hd : deriv (fun r => F r 1) 16 < 10 := by
    rw [deriv_F_radius_slope (by norm_num) (by norm_num)]
    exact radial_slope_lt_ten contact_sixteen_bracket.1 contact_sixteen_bracket.2
  exact hm.trans (by norm_num; linarith)

theorem radial_average_loss {d E : ℝ}
    (hE : 0 < E) (hd : 16 * E ≤ d) (q : ℝ) :
    (F |d - q| E + F |d + q| E) / 2 - F d E ≤ (5 / 16) * (q ^ 2 / E) := by
  have hd0 : 0 < d := by linarith
  have hx : 16 ≤ d / E := (le_div_iff₀ hE).mpr hd
  have hb := radial_ratio_le_five_sixteenths hx
  have hh := F_average_difference_le hd0 hE q
  have heq : q ^ 2 / (2 * d) * deriv (fun r => F r E) d =
      (q ^ 2 / E) * (deriv (fun r => F r 1) (d / E) / (2 * (d / E))) := by
    rw [deriv_F_radius_normalize hd0 hE]
    field_simp
  have hp := mul_le_mul_of_nonneg_left hb (show 0 ≤ q ^ 2 / E by positivity)
  rw [heq] at hh
  nlinarith only [hh, hp]

theorem endpoint_coefficient {d : ℝ} (hd : 0 ≤ d) (hdu : d ≤ 1 / 2) :
    1 / 2 ≤ endpointCoefficient d := by
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

theorem split_loss {c q : ℝ} (hc : 1 / 2 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 8 / 25) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ 3 * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (1 / 2 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (1 / 2 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  norm_num at h
  have hb := PsiThreeTenthsRetainedWedge.capacity_quadratic_five_sevenths
    (z := 13 * q / 6) (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

theorem log_thirty_nine_sevenths : (169 / 100 : ℝ) ≤ Real.log (39 / 7) := by
  have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 8)
  norm_num at h
  have he : Real.log (11 / 2 : ℝ) = 2 * Real.log 2 + Real.log (11 / 8) := by
    rw [show (11 / 2 : ℝ) = 2 ^ (2 : ℕ) * (11 / 8) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 11 / 2)
    (by norm_num : (11 / 2 : ℝ) ≤ 39 / 7)
  rw [he] at hm
  linarith

theorem logarithmic_chord {R : ℝ} (hR : 0 ≤ R) (hRu : R ≤ 32 / 5) :
    (3 / 8) * R ≤ Real.log (1 + (5 / 7) * R) / Real.log 2 := by
  have hs := strictConcaveOn_log_Ioi.concaveOn.2
    (show (39 / 7 : ℝ) ∈ Ioi 0 by norm_num) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show 0 ≤ (5 / 32) * R by positivity) (show 0 ≤ 1 - (5 / 32) * R by linarith)
    (show (5 / 32) * R + (1 - (5 / 32) * R) = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hs
  have he : (5 / 32) * R * (39 / 7) + (1 - (5 / 32) * R) * 1 =
      1 + (5 / 7) * R := by ring
  rw [he] at hs
  have hl := mul_le_mul_of_nonneg_left log_thirty_nine_sevenths
    (show 0 ≤ (5 / 32) * R by positivity)
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hm := mul_le_mul_of_nonneg_right hL hR
  apply (le_div_iff₀ log_two_pos).mpr
  nlinarith only [hs, hl, hm, hR]

theorem parent_gain {E q : ℝ} (hEl : 2 / 125 ≤ E) (hEu : E ≤ 1 / 32)
    (hq : 0 ≤ q) (hqu : q ≤ 8 / 25) :
    (3 / 8 + (10 / 7) * E) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hE : 0 < E := by linarith
  let C := 1 - H ((1 - q) / 2)
  let R := q ^ 2 / E
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRu : R ≤ 32 / 5 := by
    apply (div_le_iff₀ hE).mpr
    nlinarith only [mul_nonneg hq (show 0 ≤ 8 / 25 - q by linarith), hqu, hEl]
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
  change (3 / 8 + (10 / 7) * E) * R ≤ eta E - eta (E + C)
  nlinarith only [hl, hlog, hg, hClow, hER]

theorem retained_child_margin {d q E t : ℝ}
    (hEl : 2 / 125 ≤ E) (hEu : E ≤ 1 / 32)
    (hd : 16 * E ≤ d) (hdu : d ≤ 1 / 2)
    (hq : 0 ≤ q) (hqu : q ≤ 8 / 25) (hqd : q ≤ d) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 100) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
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
  have hr' : radialLoss d q E ≤ (5 / 16) * (q ^ 2 / E) := by
    unfold radialLoss
    linarith only [hr]
  obtain ⟨hA, hAu⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq hqd
  have hs := PsiQuarterBias.signed_split_of_loss (by linarith : 0 < endpointCoefficient d)
    hq (by norm_num : (0 : ℝ) ≤ 3) hk hloss hE hA hAu ht
  have hdec := retained_child_decomposition (C := 1 - H ((1 - q) / 2))
    hq hqd hE (by linarith) ht
  have hbudget : (5 / 16 + 3 * E + 1 / 100) * (q ^ 2 / E) ≤
      (3 / 8 + (10 / 7) * E) * (q ^ 2 / E) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have he : (5 / 16 + 3 * E + 1 / 100) * (q ^ 2 / E) =
      (5 / 16 + 1 / 100) * (q ^ 2 / E) + 3 * q ^ 2 := by
    field_simp
    ring
  rw [he] at hbudget
  linarith only [hg, hbudget, hr', hs, hdec]

/-- Actual-law closure retains both children and all feasible entropy splits. -/
theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hb : 1 / 2 ≤ μ.b)
    (hEl : 2 / 125 ≤ μ.meanEntropy) (hEu : μ.meanEntropy ≤ 1 / 32)
    (hd : 16 * μ.meanEntropy ≤ μ.b - μ.a) (hdu : μ.b - μ.a ≤ 1 / 2)
    (hq : 1 - μ.a - μ.b ≤ 8 / 25)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
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
    (hEl : 2 / 125 ≤ μ.meanEntropy) (hEu : μ.meanEntropy ≤ 1 / 32)
    (hd : 16 * μ.meanEntropy ≤ μ.b - μ.a) (hdu : μ.b - μ.a ≤ 1 / 2)
    (hq : 1 - μ.a - μ.b ≤ 8 / 25)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by linarith
  have hm := law_gap_margin μ hsum hb hEl hEu hd hdu hq hactive
  have hn : 0 ≤ (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [hm, hn]

/-- Exact complement of the newly closed high-bias central wedge. -/
def centralRegion (a b E : ℝ) : Prop :=
  PsiThreeTenthsTail28.centralRegion a b E ∧
    (1 - a - b < 3 / 10 ∨ 8 / 25 < 1 - a - b ∨ E < 2 / 125 ∨
      1 / 32 < E ∨ b - a < 16 * E)

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
    centralRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toTail28CentralOwner (h : CentralOwner) : PsiThreeTenthsTail28.CentralOwner := by
  intro k μ hab hregion hactive
  by_cases hw : 3 / 10 ≤ 1 - μ.a - μ.b ∧ 1 - μ.a - μ.b ≤ 8 / 25 ∧
      2 / 125 ≤ μ.meanEntropy ∧ μ.meanEntropy ≤ 1 / 32 ∧
      16 * μ.meanEntropy ≤ μ.b - μ.a
  · have hbase : PsiCentralAnalytic.centralRegion μ.a μ.b μ.meanEntropy :=
      hregion.1.1.1.1.1.1.1.1.1.1
    exact law_gap_le_cost μ hbase.1.le hbase.2.1 hw.2.2.1 hw.2.2.2.1
      hw.2.2.2.2 (by linarith [hbase.2.2.1, hw.1]) hw.2.1 hactive.le
  · apply h k μ hab ⟨hregion, ?_⟩ hactive
    by_contra hn
    push Not at hn
    exact hw hn

#print axioms contact_sixteen_bracket
#print axioms radial_slope_lt_ten
#print axioms radial_ratio_le_five_sixteenths
#print axioms radial_average_loss
#print axioms endpoint_coefficient
#print axioms split_loss
#print axioms log_thirty_nine_sevenths
#print axioms logarithmic_chord
#print axioms parent_gain
#print axioms retained_child_margin
#print axioms law_gap_margin
#print axioms law_gap_le_cost
#print axioms toTail28CentralOwner

end GeneralCK.PsiCentralSixteenWedge

end


