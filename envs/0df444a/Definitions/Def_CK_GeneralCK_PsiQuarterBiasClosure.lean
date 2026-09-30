-- Prove2me | Definitions.Def_CK_GeneralCK_PsiQuarterBiasClosure
-- name    : CK_GeneralCK_PsiQuarterBiasClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:18:58.784103+00:00
-- url     : https://prove2.me/theorems/55f4f9dd-f142-4043-b89b-e3f5be10b7c9
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiQuarterBiasClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiQuarterBiasClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiQuarterBiasClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiQuarterBiasClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiQuarterBiasClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiQuarterParentClosure

-- ===== source module GeneralCK.PsiQuarterBiasClosure =====
section

/-! Retained-child law closure through bias one quarter. -/

namespace GeneralCK.PsiQuarterBias
open PsiChildEntropyCoupling PsiSignedSplit

theorem endpoint_coefficient_mid {d q : ℝ} (hd : 0 ≤ d)
    (hq : 1 / 5 ≤ q) (hphysical : d + q ≤ 1) :
    3 / 7 ≤ endpointCoefficient d := by
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

theorem endpoint_coefficient_upper {d q : ℝ} (hd : 0 ≤ d)
    (hq : 2 / 9 ≤ q) (hphysical : d + q ≤ 1) :
    7 / 16 ≤ endpointCoefficient d := by
  have hL : Real.log 2 ≤ (347 / 500 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hm := mul_le_mul_of_nonneg_left hL (by linarith : 0 ≤ 1 + d)
  have hf : 250 * (1 + d) / 347 ≤ (1 + d) / (2 * Real.log 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).mpr
    nlinarith
  unfold endpointCoefficient
  linarith

theorem capacity_quadratic_five_eighths {z : ℝ}
    (hz : 0 ≤ z) (hzu : z ≤ 5 / 8) : capacity z ≤ (259 / 468) * z ^ 2 := by
  have hz1 : z < 1 := by linarith
  rw [capacity_eq_Cn (by rw [abs_of_nonneg hz]; exact hz1)]
  have hs : z ^ 2 ≤ 25 / 64 := by nlinarith
  have hn : 0 < 1 - z ^ 2 := by linarith
  have hf : z ^ 2 / (12 * (1 - z ^ 2)) ≤ (25 / 468 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - z ^ 2))).mpr
    nlinarith only [hs]
  have h := LowInformation.Cn_upper_sharp hz hz1
  have hh := mul_le_mul_of_nonneg_left hf (sq_nonneg z)
  have he : z ^ 2 * (z ^ 2 / (12 * (1 - z ^ 2))) = z ^ 4 / (12 * (1 - z ^ 2)) := by ring
  rw [he] at hh
  linarith

theorem split_loss_mid {c q : ℝ} (hc : 3 / 7 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 2 / 9) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ (16 / 5) * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (3 / 7 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (3 / 7 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  rw [show (13 * q / 6) / (2 * (3 / 7 : ℝ)) = 91 * q / 36 by ring] at h
  have hb := capacity_quadratic_five_eighths (z := 91 * q / 36) (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

theorem split_loss_upper {c q : ℝ} (hc : 7 / 16 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 4) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ (481 / 162) * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (7 / 16 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (7 / 16 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  rw [show (13 * q / 6) / (2 * (7 / 16 : ℝ)) = 52 * q / 21 by ring] at h
  have hb := capacity_quadratic_five_eighths (z := 52 * q / 21) (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

theorem signed_split_of_loss {c q E A t K : ℝ}
    (hc : 0 < c) (hq : 0 ≤ q) (hK : 0 ≤ K)
    (hk : |13 * q / 6| < 2 * c)
    (hloss : 2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ K * q ^ 2)
    (hE : 0 < E) (hA : 0 ≤ A) (hAu : A ≤ 13 * q / (3 * E)) (ht : |t| < 1) :
    -(K * q ^ 2) ≤ c * barrier t + E * t * A / 2 + (13 * q / 6) * (tilt t - t) := by
  by_cases ht0 : 0 ≤ t
  · have hb : 0 ≤ c * barrier t := mul_nonneg hc.le (barrier_nonneg ht)
    have hl : 0 ≤ E * t * A / 2 := by positivity
    have hm : 0 ≤ (13 * q / 6) * (tilt t - t) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (tilt_ge_self ht0 (abs_lt.mp ht).2))
    nlinarith [mul_nonneg hK (sq_nonneg q)]
  · have hEA : E * A ≤ 13 * q / 3 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 3 * E)).mp hAu
      nlinarith
    have hlin := mul_le_mul_of_nonpos_left hEA (le_of_not_ge ht0)
    obtain ⟨hz, _, _⟩ := objective_minimum hc hk
    have hobj := objective_lower hc.le hz (show |-t| < 1 by simpa using ht)
    rw [mul_div_cancel₀ _ (show 2 * c ≠ 0 by positivity)] at hobj
    unfold objective at hobj
    rw [barrier_neg, tilt_neg] at hobj
    nlinarith

theorem parent_gain_of_denominator {E q D : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 4)
    (hD : ((5 / 7) * (q ^ 2 / E) + 2) * Real.log 2 ≤ D) :
    ((10 / 7) / D + (10 / 7) * E) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  let C := 1 - H ((1 - q) / 2)
  let R := q ^ 2 / E
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
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
    have hh := PsiQuarterParent.parent_capacity_upper hq hqu
    change C ≤ (3 / 4) * q ^ 2 at hh
    have hs : q ^ 2 ≤ 1 / 16 := by nlinarith
    linarith only [hh, hs, hEu]
  have hg := eta_increment_ge_linear_log hE hC hphys
  have hl := Real.le_log_one_add_of_nonneg (show 0 ≤ (5 / 7) * R by positivity)
  have hm : Real.log (1 + (5 / 7) * R) ≤ Real.log (1 + C / E) :=
    Real.log_le_log (by positivity) (by linarith only [harg])
  have hlog := div_le_div_of_nonneg_right (hl.trans hm) log_two_pos.le
  have hb := div_le_div_of_nonneg_left (show 0 ≤ (10 / 7) * R by positivity)
    (by positivity : 0 < ((5 / 7) * R + 2) * Real.log 2) hD
  have he : ((10 / 7) * R) / (((5 / 7) * R + 2) * Real.log 2) =
      (2 * ((5 / 7) * R) / ((5 / 7) * R + 2)) / Real.log 2 := by
    rw [div_div]
    congr 1
    ring
  rw [he] at hb
  have hb' : ((10 / 7) / D) * R ≤
      (2 * ((5 / 7) * R) / ((5 / 7) * R + 2)) / Real.log 2 := by
    convert! hb using 1 <;> ring
  have hER : E * R = q ^ 2 := by dsimp [R]; field_simp
  change ((10 / 7) / D + (10 / 7) * E) * R ≤ eta E - eta (E + C)
  nlinarith only [hb', hlog, hg, hClow, hER]

theorem parent_gain_budget {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 4) (hqE : q ≤ 8 * E) :
    (1 / 2 + (if q ≤ 2 / 9 then 16 / 5 else 481 / 162) * E + 1 / 100) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hR : 0 ≤ q ^ 2 / E := by positivity
  by_cases hmid : q ≤ 2 / 9
  · rw [if_pos hmid]
    have hs := mul_nonneg hq (show 0 ≤ 2 / 9 - q by linarith)
    have hRu : q ^ 2 / E ≤ 16 / 9 := by
      apply (div_le_iff₀ hE).mpr
      nlinarith only [hs, hqE]
    have hD : ((5 / 7) * (q ^ 2 / E) + 2) * Real.log 2 ≤ 103 / 45 := by
      have hh := mul_le_mul (show (5 / 7) * (q ^ 2 / E) + 2 ≤ 206 / 63 by linarith)
        hL log_two_pos.le (by norm_num : (0 : ℝ) ≤ 206 / 63)
      norm_num at hh
      exact hh
    have hg := parent_gain_of_denominator hE hEu hq hqu hD
    have hm := mul_le_mul_of_nonneg_right
      (show 1 / 2 + (16 / 5) * E + 1 / 100 ≤ (10 / 7) / (103 / 45) + (10 / 7) * E by linarith) hR
    exact hm.trans hg
  · rw [if_neg hmid]
    have hs := mul_nonneg hq (show 0 ≤ 1 / 4 - q by linarith)
    have hRu : q ^ 2 / E ≤ 2 := by
      apply (div_le_iff₀ hE).mpr
      nlinarith only [hs, hqE]
    have hD : ((5 / 7) * (q ^ 2 / E) + 2) * Real.log 2 ≤ 12 / 5 := by
      have hh := mul_le_mul (show (5 / 7) * (q ^ 2 / E) + 2 ≤ 24 / 7 by linarith)
        hL log_two_pos.le (by norm_num : (0 : ℝ) ≤ 24 / 7)
      norm_num at hh
      exact hh
    have hg := parent_gain_of_denominator hE hEu hq hqu hD
    have hm := mul_le_mul_of_nonneg_right
      (show 1 / 2 + (481 / 162) * E + 1 / 100 ≤ (10 / 7) / (12 / 5) + (10 / 7) * E by linarith) hR
    exact hm.trans hg

theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEu : E ≤ 11 / 200) (hd : 8 * E ≤ d)
    (hq : 1 / 5 ≤ q) (hqu : q ≤ 1 / 4) (hqE : q ≤ 8 * E)
    (hphysical : d + q ≤ 1) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 100) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
  let K : ℝ := if q ≤ 2 / 9 then 16 / 5 else 481 / 162
  have hq0 : 0 ≤ q := by linarith
  have hqd : q ≤ d := hqE.trans hd
  have hK : 0 ≤ K := by dsimp [K]; split_ifs <;> norm_num
  have hc := endpoint_coefficient_mid (by linarith : 0 ≤ d) hq hphysical
  have hk : |13 * q / 6| < 2 * endpointCoefficient d := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have hloss : 2 * endpointCoefficient d * capacity ((13 * q / 6) / (2 * endpointCoefficient d)) ≤ K * q ^ 2 := by
    dsimp [K]
    split_ifs with hmid
    · exact split_loss_mid hc hq0 hmid
    · exact split_loss_upper (endpoint_coefficient_upper (by linarith : 0 ≤ d)
        (lt_of_not_ge hmid).le hphysical) hq0 hqu
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
  have hs := signed_split_of_loss (by linarith : 0 < endpointCoefficient d)
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
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 4)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_cases hfifth : 1 - μ.a - μ.b ≤ 1 / 5
  · exact PsiFifthBiasAutomatic.law_gap_margin μ hsum hEu hd hfifth hactive
  · have hqE := PsiQuarterParent.active_bias_lt_eight_entropy μ hq hactive
    obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
    have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
      unfold InteriorLaw.midpoint
      ring
    have hm := retained_child_margin (d := μ.b - μ.a) (q := 1 - μ.a - μ.b)
      (E := μ.meanEntropy) (t := (μ.e - μ.f) / (μ.e + μ.f)) hE hEu hd
      (lt_of_not_ge hfifth).le hq hqE.le (by linarith [μ.a_interior.1]) ht
    have hb := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
      (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
      (t := (μ.e - μ.f) / (μ.e + μ.f)) (by linarith) (hqE.le.trans hd) (by rwa [hmean])
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
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 4)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hh := law_gap_margin μ hsum hEu hd hq hactive
  have hn : 0 ≤ (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [hh, hn]

def compactRegion (a b E : ℝ) : Prop :=
  PsiFifthBiasAutomatic.compactRegion a b E ∧
    (1 - a - b ≤ 1 / 4 → 11 / 200 < E) ∧
    (1 - a - b ≤ 1 / 4 → 1 - a - b < 8 * E)

def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toAutomaticCompactOwner (h : CompactOwner) : PsiFifthBiasAutomatic.CompactOwner := by
  intro k μ hregion hactive
  by_cases hw : 1 - μ.a - μ.b ≤ 1 / 4 ∧ μ.meanEntropy ≤ 11 / 200
  · have hold := hregion.1.1.1
    exact law_gap_le_cost μ hold.1.1.1.1.le hw.2
      (by linarith [hold.1.1.1.2.2.2.1]) hw.1 hactive.le
  · apply h k μ ⟨hregion, ?_, ?_⟩ hactive
    · intro hq
      by_contra hn
      exact hw ⟨hq, le_of_not_gt hn⟩
    · intro hq
      exact PsiQuarterParent.active_bias_lt_eight_entropy μ hq hactive.le

theorem compactOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate compactRegion) : CompactOwner := by
  intro k μ hregion hactive
  have hold := hregion.1.1.1.1
  have hab : μ.a < μ.b := by
    linarith [hold.1.1.1.2.1, hold.1.1.1.2.2.2.1]
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

def centralRemainder (a b E : ℝ) : Prop :=
  (11 / 200 < E ∨ b - a < 8 * E ∨ 1 / 4 < 1 - a - b) ∧
    (1 - a - b ≤ 1 / 4 → 1 - a - b < 8 * E)

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy → 1 / 2 ≤ μ.b → 1 / 10 ≤ μ.a →
    (μ.a ≤ 1 / 10 → 1 / 32768 < μ.meanEntropy) →
    PsiCentralAnalytic.centralRemainder μ.a μ.b μ.meanEntropy →
    PsiEntropy200.centralRemainder μ.a μ.b μ.meanEntropy →
    PsiEighthBias.centralRemainder μ.a μ.b μ.meanEntropy →
    PsiSeventhBias.centralRemainder μ.a μ.b μ.meanEntropy →
    PsiSixthBias.centralRemainder μ.a μ.b μ.meanEntropy →
    PsiFifthBias.centralRemainder μ.a μ.b μ.meanEntropy →
    PsiFifthBiasAutomatic.centralRemainder μ.a μ.b μ.meanEntropy →
    centralRemainder μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toAutomaticCentralOwner (h : CentralOwner) : PsiFifthBiasAutomatic.CentralOwner := by
  intro k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇ hactive
  by_cases hw : μ.meanEntropy ≤ 11 / 200 ∧ 8 * μ.meanEntropy ≤ μ.b - μ.a ∧
      1 - μ.a - μ.b ≤ 1 / 4
  · exact law_gap_le_cost μ hsum.le hw.1 hw.2.1 hw.2.2 hactive.le
  · apply h k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇ ⟨?_, ?_⟩ hactive
    · by_contra hn
      push Not at hn
      exact hw hn
    · intro hq
      exact PsiQuarterParent.active_bias_lt_eight_entropy μ hq hactive.le

def centralRegion (a b E : ℝ) : Prop :=
  PsiFifthBiasAutomatic.centralRegion a b E ∧ centralRemainder a b E

theorem centralOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate centralRegion) : CentralOwner := by
  intro k μ hab hsum _hmean hinfo _hE hb ha _hface hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇ hr₈ hactive
  apply PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab ?_ hactive.le
  refine ⟨⟨⟨⟨⟨⟨⟨hsum, hb, ha, hinfo, hr₁, ?_⟩, hr₂, hr₃⟩, hr₄⟩, hr₅⟩, hr₆⟩, hr₇⟩, hr₈⟩
  intro hq
  exact PsiCompactAnalytic.active_bias_lt_eight_entropy μ hq hactive.le

end GeneralCK.PsiQuarterBias

#print axioms GeneralCK.PsiQuarterBias.endpoint_coefficient_mid
#print axioms GeneralCK.PsiQuarterBias.endpoint_coefficient_upper
#print axioms GeneralCK.PsiQuarterBias.capacity_quadratic_five_eighths
#print axioms GeneralCK.PsiQuarterBias.split_loss_mid
#print axioms GeneralCK.PsiQuarterBias.split_loss_upper
#print axioms GeneralCK.PsiQuarterBias.signed_split_of_loss
#print axioms GeneralCK.PsiQuarterBias.parent_gain_of_denominator
#print axioms GeneralCK.PsiQuarterBias.parent_gain_budget
#print axioms GeneralCK.PsiQuarterBias.retained_child_margin
#print axioms GeneralCK.PsiQuarterBias.law_gap_margin
#print axioms GeneralCK.PsiQuarterBias.law_gap_le_cost
#print axioms GeneralCK.PsiQuarterBias.toAutomaticCompactOwner
#print axioms GeneralCK.PsiQuarterBias.compactOwner_of_affineCertificate
#print axioms GeneralCK.PsiQuarterBias.toAutomaticCentralOwner
#print axioms GeneralCK.PsiQuarterBias.centralOwner_of_affineCertificate

end


