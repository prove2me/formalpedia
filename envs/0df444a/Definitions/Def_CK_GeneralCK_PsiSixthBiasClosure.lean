-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSixthBiasClosure
-- name    : CK_GeneralCK_PsiSixthBiasClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:16:00.898797+00:00
-- url     : https://prove2.me/theorems/7da4b5c3-92dc-4cfa-ad34-d1f5441a48ff
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSixthBiasClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSixthBiasClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSixthBiasClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSixthBiasClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSixthBiasClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiSeventhBiasClosure

-- ===== source module GeneralCK.PsiSixthBiasClosure =====
section

/-!
# Retained-child endpoint closure through parent bias one sixth

The older rational parent estimate does not pay the losses at this bias.
Keeping a stronger logarithmic lower bound gives a positive exact budget.
The parent ratio-eight exclusion uses a positive shifted cubic.
-/

namespace GeneralCK.PsiSixthBias
open Set PsiChildEntropyCoupling PsiSignedSplit

theorem logarithmic_eight_comparison {x : ℝ} (hx : 8 ≤ x) :
    2 * Real.log x < 6 * Real.log (1 + 3 * x / 25) + 1 / 7 := by
  have hy : 0 ≤ x - 8 := by linarith
  have he : (15 / 14 : ℝ) * (1 + 3 * x / 25) ^ 3 - x =
      (81 / 43750) * (x - 8) ^ 3 + (567 / 6250) * (x - 8) ^ 2 +
      (3011 / 6250) * (x - 8) + 421 / 6250 := by ring
  have hp : 0 < (15 / 14 : ℝ) * (1 + 3 * x / 25) ^ 3 - x := by rw [he]; positivity
  have hh := Real.log_lt_log (by linarith : 0 < x)
    (show x < (15 / 14 : ℝ) * (1 + 3 * x / 25) ^ 3 by linarith)
  rw [Real.log_mul (by norm_num : (15 / 14 : ℝ) ≠ 0)
    (by positivity : (1 + 3 * x / 25) ^ 3 ≠ 0), Real.log_pow] at hh
  have hc := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 15 / 14) (by norm_num : (15 / 14 : ℝ) ≠ 1)
  norm_num at hc
  linarith

/-- Sharper parent criterion, using the proved log-two bound 25/36. -/
theorem parent_dominance_of_cost_bound {q E : ℝ}
    (hq : 0 < q) (hqu : q ≤ 1 / 2) (hE : 0 < E) (hEu : E ≤ 1 / 2)
    (hbound : F q E * Real.log 2 < q ^ 2 + Real.log (1 + 18 * q ^ 2 / (25 * E))) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let C := 1 - H ((1 - q) / 2)
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hClower := SmallMean.Cn_ge_half_sq hq.le (show q ≤ 1 by linarith)
  change q ^ 2 / 2 ≤ Real.log 2 * C at hClower
  have hCrational : 18 * q ^ 2 / 25 ≤ C := by
    have hh := mul_le_mul_of_nonneg_right hL hC
    nlinarith only [hh, hClower]
  have hphysical : E + C ≤ 1 := by
    have hh := PsiParentPhiFloor.entropy_chord
      (show 0 ≤ (1 - q) / 2 by linarith) (show (1 - q) / 2 ≤ 1 / 2 by linarith)
    dsimp [C]
    linarith
  have hg := eta_increment_ge_linear_log hE hC hphysical
  have hl : Real.log (1 + 18 * q ^ 2 / (25 * E)) ≤ Real.log (1 + C / E) := by
    apply Real.log_le_log (by positivity)
    have hh := div_le_div_of_nonneg_right hCrational hE.le
    convert! add_le_add_left hh 1 using 1 <;> ring
  have hgm := mul_le_mul_of_nonneg_right hg log_two_pos.le
  have hid : (2 * C + Real.log (1 + C / E) / Real.log 2) * Real.log 2 =
      2 * C * Real.log 2 + Real.log (1 + C / E) := by field_simp
  rw [hid] at hgm
  have hF : F q E < eta E - eta (E + C) := by
    apply (mul_lt_mul_iff_left₀ log_two_pos).mp
    nlinarith only [hbound, hl, hgm, hClower]
  unfold phi psi
  rw [show |1 - 2 * ((1 - q) / 2)| = q by
    rw [show 1 - 2 * ((1 - q) / 2) = q by ring, abs_of_pos hq]]
  have he : E + 1 - H ((1 - q) / 2) = E + C := by dsimp [C]; ring
  rw [he]
  linarith only [hF]

theorem parent_dominance_ratio8 {q E : ℝ} (hq : 0 < q) (hqu : q ≤ 1 / 6)
    (hE : 0 < E) (hr : 8 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  by_cases hseventh : q ≤ 1 / 7
  · exact PsiSeventhBias.parent_dominance_ratio8 hq hseventh hE hr
  · let x := q / E
    have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hr
    have hF := (le_div_iff₀ log_two_pos).mp
      (PsiParentDominance.F_le_logarithmic_ratio8 hq hE hr)
    have hp := mul_lt_mul_of_pos_left (logarithmic_eight_comparison hx) hq
    have hs := strictConcaveOn_log_Ioi.concaveOn.2
      (show 0 < 1 + 3 * x / 25 by positivity)
      (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (show 0 ≤ 6 * q by positivity) (show 0 ≤ 1 - 6 * q by linarith)
      (show 6 * q + (1 - 6 * q) = 1 by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hs
    have hs' : 6 * q * Real.log (1 + 3 * x / 25) ≤
        Real.log (1 + 18 * q ^ 2 / (25 * E)) := by
      convert! hs using 1
      congr 1
      dsimp [x]
      ring
    apply parent_dominance_of_cost_bound hq (by linarith) hE (by linarith)
    change F q E * Real.log 2 ≤ 2 * q * Real.log x at hF
    have hlinear := mul_nonneg hq.le (show 0 ≤ q - 1 / 7 by linarith [lt_of_not_ge hseventh])
    nlinarith only [hF, hp, hs', hlinear]

theorem active_bias_lt_eight_entropy {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hq : 1 - μ.a - μ.b ≤ 1 / 6)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    1 - μ.a - μ.b < 8 * μ.meanEntropy := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_contra hn
  have h := parent_dominance_ratio8 (by linarith [le_of_not_gt hn]) hq hE (le_of_not_gt hn)
  have hm : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  rw [hm] at h
  exact (not_lt_of_ge hactive) h

theorem split_loss_upper {c q : ℝ} (hc : 39 / 100 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 6) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ (16 / 5) * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (39 / 100 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (39 / 100 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  rw [show (13 * q / 6) / (2 * (39 / 100 : ℝ)) = 325 * q / 117 by ring] at h
  have hb := PsiEighthBias.capacity_quadratic_half
    (z := 325 * q / 117) (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

theorem objective_lower_bound {c q t : ℝ} (hc : 39 / 100 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 6) (ht : |t| < 1) :
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
    (hc : 39 / 100 ≤ c) (hq : 0 ≤ q) (hqu : q ≤ 1 / 6)
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
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 6) :
    E + (1 - H ((1 - q) / 2)) ≤ 1 := by
  rcases hq.eq_or_lt with he | hp
  · rw [← he]
    norm_num [H_half]
    linarith
  · have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
    have hs := mul_nonneg hq (show 0 ≤ 1 / 6 - q by linarith)
    nlinarith

/-- The stronger log(1+x) lower bound preserves a uniform positive budget. -/
theorem parent_gain_logarithmic {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 6) (hqE : q ≤ 8 * E) :
    (150 / 217) * (q ^ 2 / E) ≤
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
  have hs := mul_nonneg hq (show 0 ≤ 1 / 6 - q by linarith)
  have hRu : R ≤ 4 / 3 := by
    apply (div_le_iff₀ hE).mpr
    nlinarith only [hs, hqE]
  have hd : ((5 / 7) * R + 2) * Real.log 2 ≤ 31 / 15 := by
    have hh := mul_le_mul (show (5 / 7) * R + 2 ≤ 62 / 21 by linarith)
      hL log_two_pos.le (by norm_num : (0 : ℝ) ≤ 62 / 21)
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
  have hb' : (150 / 217) * R ≤
      (2 * ((5 / 7) * R) / ((5 / 7) * R + 2)) / Real.log 2 := by
    convert! hb using 1 <;> ring
  change (150 / 217) * R ≤ eta E - eta (E + C)
  linarith only [hb', hlog, hg, hC]

theorem parent_gain_budget {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 6) (hqE : q ≤ 8 * E) :
    (1 / 2 + (16 / 5) * E + 1 / 100) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hg := parent_gain_logarithmic hE hEu hq hqu hqE
  have hm := mul_le_mul_of_nonneg_right
    (show 1 / 2 + (16 / 5) * E + 1 / 100 ≤ (150 / 217 : ℝ) by linarith)
    (show 0 ≤ q ^ 2 / E by positivity)
  exact hm.trans hg

theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEu : E ≤ 11 / 200) (hd : 8 * E ≤ d)
    (hq : 1 / 8 ≤ q) (hqu : q ≤ 1 / 6) (hqE : q ≤ 8 * E)
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
  have hc := PsiSeventhBias.endpoint_coefficient_lower (by linarith : 0 ≤ d) hq hphysical
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
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 6)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_cases heighth : 1 - μ.a - μ.b ≤ 1 / 8
  · exact PsiEighthBias.law_gap_margin μ hsum hEu hd heighth hactive
  · have hqE := active_bias_lt_eight_entropy μ hq hactive
    obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
    have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
      unfold InteriorLaw.midpoint
      ring
    have hm := retained_child_margin (d := μ.b - μ.a) (q := 1 - μ.a - μ.b)
      (E := μ.meanEntropy) (t := (μ.e - μ.f) / (μ.e + μ.f)) hE hEu hd
      (lt_of_not_ge heighth).le hq hqE.le (by linarith [μ.a_interior.1]) ht
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
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 6)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hh := law_gap_margin μ hsum hEu hd hq hactive
  have hn : 0 ≤ (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [hh, hn]

def compactRegion (a b E : ℝ) : Prop :=
  PsiSeventhBias.compactRegion a b E ∧
    (1 - a - b ≤ 1 / 6 → 11 / 200 < E) ∧
    (1 - a - b ≤ 1 / 6 → 1 - a - b < 8 * E)

def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toSeventhCompactOwner (h : CompactOwner) : PsiSeventhBias.CompactOwner := by
  intro k μ hregion hactive
  by_cases hw : 1 - μ.a - μ.b ≤ 1 / 6 ∧ μ.meanEntropy ≤ 11 / 200
  · exact law_gap_le_cost μ hregion.1.1.1.1.le hw.2
      (by linarith [hregion.1.1.1.2.2.2.1]) hw.1 hactive.le
  · apply h k μ ⟨hregion, ?_, ?_⟩ hactive
    · intro hq
      by_contra hn
      exact hw ⟨hq, le_of_not_gt hn⟩
    · intro hq
      exact active_bias_lt_eight_entropy μ hq hactive.le

theorem compactOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate compactRegion) : CompactOwner := by
  intro k μ hregion hactive
  have hab : μ.a < μ.b := by
    linarith [hregion.1.1.1.1.2.1, hregion.1.1.1.1.2.2.2.1]
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

def centralRemainder (a b E : ℝ) : Prop :=
  (11 / 200 < E ∨ b - a < 8 * E ∨ 1 / 6 < 1 - a - b) ∧
    (1 - a - b ≤ 1 / 6 → 1 - a - b < 8 * E)

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
    centralRemainder μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toSeventhCentralOwner (h : CentralOwner) : PsiSeventhBias.CentralOwner := by
  intro k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hr₃ hr₄ hactive
  by_cases hw : μ.meanEntropy ≤ 11 / 200 ∧ 8 * μ.meanEntropy ≤ μ.b - μ.a ∧
      1 - μ.a - μ.b ≤ 1 / 6
  · exact law_gap_le_cost μ hsum.le hw.1 hw.2.1 hw.2.2 hactive.le
  · apply h k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hr₃ hr₄ ⟨?_, ?_⟩ hactive
    · by_contra hn
      push Not at hn
      exact hw hn
    · intro hq
      exact active_bias_lt_eight_entropy μ hq hactive.le

def centralRegion (a b E : ℝ) : Prop :=
  PsiSeventhBias.centralRegion a b E ∧ centralRemainder a b E

theorem centralOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate centralRegion) : CentralOwner := by
  intro k μ hab hsum _hmean hinfo _hE hb ha _hface hr₁ hr₂ hr₃ hr₄ hr₅ hactive
  apply PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab ?_ hactive.le
  refine ⟨⟨⟨⟨hsum, hb, ha, hinfo, hr₁, ?_⟩, hr₂, hr₃⟩, hr₄⟩, hr₅⟩
  intro hq
  exact PsiCompactAnalytic.active_bias_lt_eight_entropy μ hq hactive.le

end GeneralCK.PsiSixthBias

namespace GeneralCK

/-- The remaining active-psi owners after the proved sixth-bias wedge. -/
structure ResidualPsiSixthBiasRemainingOwners : Prop where
  sameChart : SameSidePsiExtendedChartOwner
  oppositeCentral : PsiSixthBias.CentralOwner
  oppositeCompact : PsiSixthBias.CompactOwner

theorem ResidualPsiSixthBiasRemainingOwners.toSeventhBias
    (h : ResidualPsiSixthBiasRemainingOwners) :
    ResidualPsiSeventhBiasRemainingOwners where
  sameChart := h.sameChart
  oppositeCentral := PsiSixthBias.toSeventhCentralOwner h.oppositeCentral
  oppositeCompact := PsiSixthBias.toSeventhCompactOwner h.oppositeCompact

end GeneralCK

#print axioms GeneralCK.PsiSixthBias.logarithmic_eight_comparison
#print axioms GeneralCK.PsiSixthBias.parent_dominance_of_cost_bound
#print axioms GeneralCK.PsiSixthBias.parent_dominance_ratio8
#print axioms GeneralCK.PsiSixthBias.active_bias_lt_eight_entropy
#print axioms GeneralCK.PsiSixthBias.split_loss_upper
#print axioms GeneralCK.PsiSixthBias.objective_lower_bound
#print axioms GeneralCK.PsiSixthBias.signed_split_lower
#print axioms GeneralCK.PsiSixthBias.parent_physical
#print axioms GeneralCK.PsiSixthBias.parent_gain_logarithmic
#print axioms GeneralCK.PsiSixthBias.parent_gain_budget
#print axioms GeneralCK.PsiSixthBias.retained_child_margin
#print axioms GeneralCK.PsiSixthBias.law_gap_margin
#print axioms GeneralCK.PsiSixthBias.law_gap_le_cost
#print axioms GeneralCK.PsiSixthBias.toSeventhCompactOwner
#print axioms GeneralCK.PsiSixthBias.compactOwner_of_affineCertificate
#print axioms GeneralCK.PsiSixthBias.toSeventhCentralOwner
#print axioms GeneralCK.PsiSixthBias.centralOwner_of_affineCertificate
#print axioms GeneralCK.ResidualPsiSixthBiasRemainingOwners.toSeventhBias

end


