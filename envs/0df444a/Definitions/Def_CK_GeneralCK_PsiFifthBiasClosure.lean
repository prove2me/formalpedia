-- Prove2me | Definitions.Def_CK_GeneralCK_PsiFifthBiasClosure
-- name    : CK_GeneralCK_PsiFifthBiasClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:21:00.668453+00:00
-- url     : https://prove2.me/theorems/788ea5ec-3b3a-4eaa-9d58-d0dd18e1739e
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiFifthBiasClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiFifthBiasClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiFifthBiasClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiFifthBiasClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiFifthBiasClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiSixthBiasClosure

-- ===== source module GeneralCK.PsiFifthBiasClosure =====
section

/-!
# Retained-child closure through bias one fifth with explicit ratio face

Keeping the linear parent entropy gain closes q <= 1/5 when q <= 8E.
Unlike the sixth-bias theorem, the new ratio face is an explicit hypothesis;
no parent dominance claim on its complement is made here.
-/

namespace GeneralCK.PsiFifthBias
open PsiChildEntropyCoupling PsiSignedSplit

/-- At q=1/5 and E=1/40, the old coarse F envelope exceeds the available
parent comparison. This obstructs that estimate, not the Bellman inequality. -/
theorem coarse_ratio8_parent_budget_fails :
    (1 / 25 : ℝ) + Real.log (269 / 125) < (2 / 5) * Real.log 8 := by
  have hL : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 269 / 250)
  norm_num at hlog
  rw [show (269 / 125 : ℝ) = 2 * (269 / 250) by norm_num,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (269 / 250 : ℝ) ≠ 0),
    show Real.log 8 = 3 * Real.log 2 by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num]
  linarith only [hL, hlog]

theorem endpoint_coefficient_lower {d q : ℝ} (hd : 0 ≤ d)
    (hq : 1 / 6 ≤ q) (hphysical : d + q ≤ 1) :
    2 / 5 ≤ endpointCoefficient d := by
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hm := mul_le_mul_of_nonneg_left hL (by linarith : 0 ≤ 1 + d)
  have hf : 5 * (1 + d) / 7 ≤ (1 + d) / (2 * Real.log 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).mpr
    nlinarith
  unfold endpointCoefficient
  linarith

theorem capacity_quadratic_eleven_twentieths {z : ℝ}
    (hz : 0 ≤ z) (hzu : z ≤ 11 / 20) :
    capacity z ≤ (27 / 50) * z ^ 2 := by
  have hz1 : z < 1 := by linarith
  rw [capacity_eq_Cn (by rw [abs_of_nonneg hz]; exact hz1)]
  have hs : z ^ 2 ≤ 121 / 400 := by nlinarith
  have hn : 0 < 1 - z ^ 2 := by nlinarith
  have hf : z ^ 2 / (12 * (1 - z ^ 2)) ≤ (1 / 25 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - z ^ 2))).mpr
    nlinarith only [hs]
  have h := LowInformation.Cn_upper_sharp hz hz1
  have hh := mul_le_mul_of_nonneg_left hf (sq_nonneg z)
  have he : z ^ 2 * (z ^ 2 / (12 * (1 - z ^ 2))) =
      z ^ 4 / (12 * (1 - z ^ 2)) := by ring
  rw [he] at hh
  linarith

theorem split_loss_upper {c q : ℝ} (hc : 2 / 5 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 5) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ (16 / 5) * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (2 / 5 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (2 / 5 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  rw [show (13 * q / 6) / (2 * (2 / 5 : ℝ)) = 65 * q / 24 by ring] at h
  have hb := capacity_quadratic_eleven_twentieths
    (z := 65 * q / 24) (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

theorem objective_lower_bound {c q t : ℝ} (hc : 2 / 5 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 5) (ht : |t| < 1) :
    -((16 / 5) * q ^ 2) ≤ objective c (13 * q / 6) t := by
  have hcpos : 0 < c := by linarith
  have hk : |13 * q / 6| < 2 * c := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  obtain ⟨hz, _, _⟩ := objective_minimum hcpos hk
  have h := objective_lower hcpos.le hz ht
  rw [mul_div_cancel₀ _ (show 2 * c ≠ 0 by positivity)] at h
  linarith [split_loss_upper hc hq hqu]

theorem signed_split_lower {c q E A t : ℝ}
    (hc : 2 / 5 ≤ c) (hq : 0 ≤ q) (hqu : q ≤ 1 / 5)
    (hE : 0 < E) (hA : 0 ≤ A) (hAu : A ≤ 13 * q / (3 * E)) (ht : |t| < 1) :
    -((16 / 5) * q ^ 2) ≤
      c * barrier t + E * t * A / 2 + (13 * q / 6) * (tilt t - t) := by
  by_cases ht0 : 0 ≤ t
  · have hb : 0 ≤ c * barrier t := mul_nonneg (by linarith) (barrier_nonneg ht)
    have hl : 0 ≤ E * t * A / 2 := by positivity
    have hm : 0 ≤ (13 * q / 6) * (tilt t - t) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (tilt_ge_self ht0 (abs_lt.mp ht).2))
    nlinarith [sq_nonneg q]
  · have hEA : E * A ≤ 13 * q / 3 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 3 * E)).mp hAu
      nlinarith
    have hlin := mul_le_mul_of_nonpos_left hEA (le_of_not_ge ht0)
    have hobj := objective_lower_bound (t := -t) hc hq hqu (by simpa using ht)
    unfold objective at hobj
    rw [barrier_neg, tilt_neg] at hobj
    nlinarith

theorem parent_physical {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 5) :
    E + (1 - H ((1 - q) / 2)) ≤ 1 := by
  rcases hq.eq_or_lt with he | hp
  · rw [← he]
    norm_num [H_half]
    linarith
  · have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
    have hs := mul_nonneg hq (show 0 ≤ 1 / 5 - q by linarith)
    nlinarith

theorem parent_gain_logarithmic {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 5) (hqE : q ≤ 8 * E) :
    (50 / 77 + (10 / 7) * E) * (q ^ 2 / E) ≤
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
  have hg := eta_increment_ge_linear_log hE hC (parent_physical hE hEu hq hqu)
  have hl := Real.le_log_one_add_of_nonneg (show 0 ≤ (5 / 7) * R by positivity)
  have hm : Real.log (1 + (5 / 7) * R) ≤ Real.log (1 + C / E) :=
    Real.log_le_log (by positivity) (by linarith only [harg])
  have hlog := div_le_div_of_nonneg_right (hl.trans hm) log_two_pos.le
  have hs := mul_nonneg hq (show 0 ≤ 1 / 5 - q by linarith)
  have hRu : R ≤ 8 / 5 := by
    apply (div_le_iff₀ hE).mpr
    nlinarith only [hs, hqE]
  have hd : ((5 / 7) * R + 2) * Real.log 2 ≤ 11 / 5 := by
    have hh := mul_le_mul (show (5 / 7) * R + 2 ≤ 22 / 7 by linarith)
      hL log_two_pos.le (by norm_num : (0 : ℝ) ≤ 22 / 7)
    norm_num at hh
    exact hh
  have hb := div_le_div_of_nonneg_left (show 0 ≤ (10 / 7) * R by positivity)
    (by positivity : 0 < ((5 / 7) * R + 2) * Real.log 2) hd
  have he : ((10 / 7) * R) / (((5 / 7) * R + 2) * Real.log 2) =
      (2 * ((5 / 7) * R) / ((5 / 7) * R + 2)) / Real.log 2 := by
    rw [div_div]
    congr 1
    ring
  rw [he] at hb
  have hb' : (50 / 77) * R ≤
      (2 * ((5 / 7) * R) / ((5 / 7) * R + 2)) / Real.log 2 := by
    convert! hb using 1 <;> ring
  have hER : E * R = q ^ 2 := by dsimp [R]; field_simp
  change (50 / 77 + (10 / 7) * E) * R ≤ eta E - eta (E + C)
  nlinarith only [hb', hlog, hg, hClow, hER]

theorem parent_gain_budget {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 5) (hqE : q ≤ 8 * E) :
    (1 / 2 + (16 / 5) * E + 1 / 100) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hg := parent_gain_logarithmic hE hEu hq hqu hqE
  have hm := mul_le_mul_of_nonneg_right
    (show 1 / 2 + (16 / 5) * E + 1 / 100 ≤ (50 / 77 + (10 / 7) * E : ℝ) by linarith)
    (show 0 ≤ q ^ 2 / E by positivity)
  exact hm.trans hg

theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEu : E ≤ 11 / 200) (hd : 8 * E ≤ d)
    (hq : 1 / 6 ≤ q) (hqu : q ≤ 1 / 5) (hqE : q ≤ 8 * E)
    (hphysical : d + q ≤ 1) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 100) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
  have hq0 : 0 ≤ q := by linarith
  have hqd : q ≤ d := hqE.trans hd
  have hg := parent_gain_budget hE hEu hq0 hqu hqE
  have hr := PsiRadialDeficit.radial_average_loss_le_half hE hd q
  rw [abs_of_nonneg (show 0 ≤ d - q by linarith),
    abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
  have hr' : radialLoss d q E ≤ (q ^ 2 / E) / 2 := by
    rw [show q ^ 2 / (2 * E) = (q ^ 2 / E) / 2 by ring] at hr
    unfold radialLoss
    linarith only [hr]
  obtain ⟨hA, hAu⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq0 hqd
  have hc := endpoint_coefficient_lower (by linarith : 0 ≤ d) hq hphysical
  have hs := signed_split_lower hc hq0 hqu hE hA hAu ht
  have hdec := retained_child_decomposition (C := 1 - H ((1 - q) / 2)) hq0 hqd hE hEu ht
  have he : (1 / 2 + (16 / 5) * E + 1 / 100) * (q ^ 2 / E) =
      (1 / 2 + 1 / 100) * (q ^ 2 / E) + (16 / 5) * q ^ 2 := by
    field_simp
    ring
  rw [he] at hg
  linarith only [hg, hr', hs, hdec]

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEu : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 5)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_cases hsixth : 1 - μ.a - μ.b ≤ 1 / 6
  · exact PsiSixthBias.law_gap_margin μ hsum hEu hd hsixth hactive
  · obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
    have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
      unfold InteriorLaw.midpoint
      ring
    have hm := retained_child_margin (d := μ.b - μ.a) (q := 1 - μ.a - μ.b)
      (E := μ.meanEntropy) (t := (μ.e - μ.f) / (μ.e + μ.f)) hE hEu hd
      (lt_of_not_ge hsixth).le hq hqE (by linarith [μ.a_interior.1]) ht
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
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 5)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hh := law_gap_margin μ hsum hEu hd hq hqE hactive
  have hn : 0 ≤ (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [hh, hn]

/-- The fifth-bias wedge is removed only on its explicitly proved ratio face. -/
def compactRegion (a b E : ℝ) : Prop :=
  PsiSixthBias.compactRegion a b E ∧
    (1 - a - b ≤ 1 / 5 → 11 / 200 < E ∨ 8 * E < 1 - a - b)

def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toSixthCompactOwner (h : CompactOwner) : PsiSixthBias.CompactOwner := by
  intro k μ hregion hactive
  by_cases hw : 1 - μ.a - μ.b ≤ 1 / 5 ∧ μ.meanEntropy ≤ 11 / 200 ∧
      1 - μ.a - μ.b ≤ 8 * μ.meanEntropy
  · have hold := hregion.1
    exact law_gap_le_cost μ hold.1.1.1.1.le hw.2.1
      (by linarith [hold.1.1.1.2.2.2.1]) hw.1 hw.2.2 hactive.le
  · apply h k μ ⟨hregion, ?_⟩ hactive
    intro hq
    by_contra hn
    push Not at hn
    exact hw ⟨hq, hn⟩

theorem compactOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate compactRegion) : CompactOwner := by
  intro k μ hregion hactive
  have hold := hregion.1.1
  have hab : μ.a < μ.b := by
    linarith [hold.1.1.1.2.1, hold.1.1.1.2.2.2.1]
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

def centralRemainder (a b E : ℝ) : Prop :=
  11 / 200 < E ∨ b - a < 8 * E ∨ 1 / 5 < 1 - a - b ∨ 8 * E < 1 - a - b

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
    centralRemainder μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toSixthCentralOwner (h : CentralOwner) : PsiSixthBias.CentralOwner := by
  intro k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hr₃ hr₄ hr₅ hactive
  by_cases hw : μ.meanEntropy ≤ 11 / 200 ∧ 8 * μ.meanEntropy ≤ μ.b - μ.a ∧
      1 - μ.a - μ.b ≤ 1 / 5 ∧ 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy
  · exact law_gap_le_cost μ hsum.le hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 hactive.le
  · apply h k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hr₃ hr₄ hr₅ ?_ hactive
    by_contra hn
    unfold centralRemainder at hn
    push Not at hn
    exact hw hn

def centralRegion (a b E : ℝ) : Prop :=
  PsiSixthBias.centralRegion a b E ∧ centralRemainder a b E

theorem centralOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate centralRegion) : CentralOwner := by
  intro k μ hab hsum _hmean hinfo _hE hb ha _hface hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hactive
  apply PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab ?_ hactive.le
  refine ⟨⟨⟨⟨⟨hsum, hb, ha, hinfo, hr₁, ?_⟩, hr₂, hr₃⟩, hr₄⟩, hr₅⟩, hr₆⟩
  intro hq
  exact PsiCompactAnalytic.active_bias_lt_eight_entropy μ hq hactive.le

end GeneralCK.PsiFifthBias

namespace GeneralCK

/-- The remaining active-psi owners after the proved fifth-bias wedge. -/
structure ResidualPsiFifthBiasRemainingOwners : Prop where
  sameChart : SameSidePsiExtendedChartOwner
  oppositeCentral : PsiFifthBias.CentralOwner
  oppositeCompact : PsiFifthBias.CompactOwner

theorem ResidualPsiFifthBiasRemainingOwners.toSixthBias
    (h : ResidualPsiFifthBiasRemainingOwners) :
    ResidualPsiSixthBiasRemainingOwners where
  sameChart := h.sameChart
  oppositeCentral := PsiFifthBias.toSixthCentralOwner h.oppositeCentral
  oppositeCompact := PsiFifthBias.toSixthCompactOwner h.oppositeCompact

end GeneralCK

#print axioms GeneralCK.PsiFifthBias.coarse_ratio8_parent_budget_fails
#print axioms GeneralCK.PsiFifthBias.endpoint_coefficient_lower
#print axioms GeneralCK.PsiFifthBias.capacity_quadratic_eleven_twentieths
#print axioms GeneralCK.PsiFifthBias.split_loss_upper
#print axioms GeneralCK.PsiFifthBias.objective_lower_bound
#print axioms GeneralCK.PsiFifthBias.signed_split_lower
#print axioms GeneralCK.PsiFifthBias.parent_physical
#print axioms GeneralCK.PsiFifthBias.parent_gain_logarithmic
#print axioms GeneralCK.PsiFifthBias.parent_gain_budget
#print axioms GeneralCK.PsiFifthBias.retained_child_margin
#print axioms GeneralCK.PsiFifthBias.law_gap_margin
#print axioms GeneralCK.PsiFifthBias.law_gap_le_cost
#print axioms GeneralCK.PsiFifthBias.toSixthCompactOwner
#print axioms GeneralCK.PsiFifthBias.compactOwner_of_affineCertificate
#print axioms GeneralCK.PsiFifthBias.toSixthCentralOwner
#print axioms GeneralCK.PsiFifthBias.centralOwner_of_affineCertificate
#print axioms GeneralCK.ResidualPsiFifthBiasRemainingOwners.toSixthBias


end


