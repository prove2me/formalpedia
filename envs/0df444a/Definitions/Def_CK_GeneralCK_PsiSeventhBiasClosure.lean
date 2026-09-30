-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSeventhBiasClosure
-- name    : CK_GeneralCK_PsiSeventhBiasClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:10:35.385119+00:00
-- url     : https://prove2.me/theorems/9cea51a1-724d-48f4-a083-c923139721b4
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSeventhBiasClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSeventhBiasClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSeventhBiasClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSeventhBiasClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSeventhBiasClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiEighthBiasClosure

-- ===== source module GeneralCK.PsiSeventhBiasClosure =====
section

/-!
# Retained-child endpoint closure through parent bias one seventh

The physical relation d+q≤1 improves the signed-split coefficient on the
new strip q≥1/8. A new ratio-eight parent exclusion and exact quadratic
parent-gain budget close this strip with all entropy allocations retained.
-/

namespace GeneralCK.PsiSeventhBias
open PsiChildEntropyCoupling PsiSignedSplit

theorem logarithmic_eight_comparison {x : ℝ} (hx : 8 ≤ x) :
    2 * Real.log x < 7 * Real.log (1 + 5 * x / 49) := by
  have hy : 0 ≤ x - 8 := by linarith
  have he : (1 + 5 * x / 49) ^ 7 - x ^ 2 =
      (78125 / 678223072849 : ℝ) * (x - 8) ^ 7 +
      (1390625 / 96889010407) * (x - 8) ^ 6 +
      (74259375 / 96889010407) * (x - 8) ^ 5 +
      (2203028125 / 96889010407) * (x - 8) ^ 4 +
      (39213900625 / 96889010407) * (x - 8) ^ 3 +
      (321915448268 / 96889010407) * (x - 8) ^ 2 +
      (934682288293 / 96889010407) * (x - 8) +
      825058233193 / 678223072849 := by ring
  have hp : 0 < (1 + 5 * x / 49) ^ 7 - x ^ 2 := by rw [he]; positivity
  have hh := Real.log_lt_log (by positivity : 0 < x ^ 2)
    (show x ^ 2 < (1 + 5 * x / 49) ^ 7 by linarith)
  rw [Real.log_pow, Real.log_pow] at hh
  exact hh

theorem parent_dominance_ratio8 {q E : ℝ} (hq : 0 < q) (hqu : q ≤ 1 / 7)
    (hE : 0 < E) (hr : 8 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let x := q / E
  have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hr
  have hF := (le_div_iff₀ log_two_pos).mp
    (PsiParentDominance.F_le_logarithmic_ratio8 hq hE hr)
  have hp := mul_lt_mul_of_pos_left (logarithmic_eight_comparison hx) hq
  have hs := PsiOuterEntropy200.logarithmic_bias_scale (Q := (1 / 7 : ℝ))
    hq.le (by norm_num) hqu (show 0 ≤ x by linarith)
  have hs' : 7 * q * Real.log (1 + 5 * x / 49) ≤
      Real.log (1 + 5 * q ^ 2 / (7 * E)) := by
    convert! hs using 1 <;> dsimp [x] <;> congr 1 <;> ring
  apply PsiOuterEntropy200.parent_dominance_of_cost_bound hq (by linarith)
    hE (by linarith)
  change F q E * Real.log 2 ≤ 2 * q * Real.log x at hF
  nlinarith only [hF, hp, hs', sq_nonneg q]

theorem active_bias_lt_eight_entropy {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hq : 1 - μ.a - μ.b ≤ 1 / 7)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    1 - μ.a - μ.b < 8 * μ.meanEntropy := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_contra hn
  have hr := le_of_not_gt hn
  have h := parent_dominance_ratio8 (by linarith) hq hE hr
  have hm : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  rw [hm] at h
  exact (not_lt_of_ge hactive) h

theorem endpoint_coefficient_lower {d q : ℝ} (hd : 0 ≤ d)
    (hq : 1 / 8 ≤ q) (hphysical : d + q ≤ 1) :
    39 / 100 ≤ endpointCoefficient d := by
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

theorem split_loss_upper {c q : ℝ} (hc : 39 / 100 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 7) :
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
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 7) (ht : |t| < 1) :
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
    (hc : 39 / 100 ≤ c) (hq : 0 ≤ q) (hqu : q ≤ 1 / 7)
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
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 7) :
    E + (1 - H ((1 - q) / 2)) ≤ 1 := by
  rcases hq.eq_or_lt with he | hp
  · rw [← he]
    norm_num [H_half]
    linarith
  · have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
    have hs := mul_nonneg hq (show 0 ≤ 1 / 7 - q by linarith)
    nlinarith

/-- The parent gain pays radial loss, the sharper signed loss, and a margin. -/
theorem parent_gain_budget {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 7) (hqE : q ≤ 8 * E) :
    (1 / 2 + (16 / 5) * E + 1 / 500) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hg := PsiLargerEntropyRedesign.parent_gain_rational hE hq (by linarith)
    (parent_physical hE hEu hq hqu)
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hLsq : (Real.log 2) ^ 2 ≤ (49 / 100 : ℝ) := by nlinarith [log_two_pos]
  let D := Real.log 2 * (2 * Real.log 2 * E + q ^ 2)
  let c := 1 / 2 + (16 / 5) * E + 1 / 500
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hden : D ≤ (49 / 50) * E + (7 / 10) * q ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hLsq hE.le
    have h2 := mul_le_mul_of_nonneg_right hL (sq_nonneg q)
    dsimp [D]
    nlinarith only [h1, h2]
  have hs := mul_nonneg hq (show 0 ≤ 1 / 7 - q by linarith)
  have hsq : q ^ 2 ≤ 1 / 49 := by nlinarith
  have hsqE : q ^ 2 ≤ (8 / 7) * E := by nlinarith only [hs, hqE]
  have hbudget : c * D ≤ E := by
    by_cases hlo : E ≤ 1 / 56
    · have hd : D ≤ (89 / 50) * E := by nlinarith only [hden, hsqE]
      have hcu : c ≤ 50 / 89 := by dsimp [c]; linarith
      have h1 := mul_le_mul_of_nonneg_left hd hc
      have h2 := mul_le_mul_of_nonneg_right hcu hE.le
      nlinarith only [h1, h2]
    · have hd : D ≤ (49 / 50) * E + 1 / 70 := by nlinarith only [hden, hsq]
      have hp : (1 / 2 + (16 / 5) * E + 1 / 500) *
          ((49 / 50) * E + 1 / 70) ≤ E := by
        have hh := mul_nonneg (show 0 ≤ E - 1 / 56 by linarith [lt_of_not_ge hlo])
          (show 0 ≤ 11 / 200 - E by linarith)
        nlinarith only [hh, hEu, show 1 / 56 ≤ E by linarith [lt_of_not_ge hlo]]
      exact (mul_le_mul_of_nonneg_left hd hc).trans hp
  have hco : c ≤ E / D := (le_div_iff₀ hD).mpr hbudget
  have hn : 0 ≤ q ^ 2 / E := by positivity
  calc
    _ ≤ (E / D) * (q ^ 2 / E) := mul_le_mul_of_nonneg_right hco hn
    _ = q ^ 2 / D := by field_simp
    _ ≤ _ := hg

theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEu : E ≤ 11 / 200) (hd : 8 * E ≤ d)
    (hq : 1 / 8 ≤ q) (hqu : q ≤ 1 / 7) (hqE : q ≤ 8 * E)
    (hphysical : d + q ≤ 1) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 500) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
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
  have he : (1 / 2 + (16 / 5) * E + 1 / 500) * (q ^ 2 / E) =
      (1 / 2 + 1 / 500) * (q ^ 2 / E) + (16 / 5) * q ^ 2 := by
    field_simp
    ring
  rw [he] at hg
  linarith only [hg, hr', hs, hdec]

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEu : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 7)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 500) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_cases heighth : 1 - μ.a - μ.b ≤ 1 / 8
  · have h := PsiEighthBias.law_gap_margin μ hsum hEu hd heighth hactive
    have hn : 0 ≤ (1 - μ.a - μ.b) ^ 2 / μ.meanEntropy := by positivity
    linarith only [h, hn]
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
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 7)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hh := law_gap_margin μ hsum hEu hd hq hactive
  have hn : 0 ≤ (1 / 500) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [hh, hn]

/-- The old compact remainder, clipped by the new closed owner and by the
new proved active-parent ratio exclusion. -/
def compactRegion (a b E : ℝ) : Prop :=
  PsiEighthBias.compactRegion a b E ∧
    (1 - a - b ≤ 1 / 7 → 11 / 200 < E) ∧
    (1 - a - b ≤ 1 / 7 → 1 - a - b < 8 * E)

def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toEighthCompactOwner (h : CompactOwner) : PsiEighthBias.CompactOwner := by
  intro k μ hregion hactive
  by_cases hw : 1 - μ.a - μ.b ≤ 1 / 7 ∧ μ.meanEntropy ≤ 11 / 200
  · exact law_gap_le_cost μ hregion.1.1.1.le hw.2
      (by linarith [hregion.1.1.2.2.2.1]) hw.1 hactive.le
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
    linarith [hregion.1.1.1.2.1, hregion.1.1.1.2.2.2.1]
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

def centralRemainder (a b E : ℝ) : Prop :=
  (11 / 200 < E ∨ b - a < 8 * E ∨ 1 / 7 < 1 - a - b) ∧
    (1 - a - b ≤ 1 / 7 → 1 - a - b < 8 * E)

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy → 1 / 2 ≤ μ.b → 1 / 10 ≤ μ.a →
    (μ.a ≤ 1 / 10 → 1 / 32768 < μ.meanEntropy) →
    PsiCentralAnalytic.centralRemainder μ.a μ.b μ.meanEntropy →
    PsiEntropy200.centralRemainder μ.a μ.b μ.meanEntropy →
    PsiEighthBias.centralRemainder μ.a μ.b μ.meanEntropy →
    centralRemainder μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toEighthCentralOwner (h : CentralOwner) : PsiEighthBias.CentralOwner := by
  intro k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hr₃ hactive
  by_cases hw : μ.meanEntropy ≤ 11 / 200 ∧ 8 * μ.meanEntropy ≤ μ.b - μ.a ∧
      1 - μ.a - μ.b ≤ 1 / 7
  · exact law_gap_le_cost μ hsum.le hw.1 hw.2.1 hw.2.2 hactive.le
  · apply h k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hr₃ ⟨?_, ?_⟩ hactive
    · by_contra hn
      push Not at hn
      exact hw hn
    · intro hq
      exact active_bias_lt_eight_entropy μ hq hactive.le

def centralRegion (a b E : ℝ) : Prop :=
  PsiEighthBias.centralRegion a b E ∧ centralRemainder a b E

theorem centralOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate centralRegion) : CentralOwner := by
  intro k μ hab hsum _hmean hinfo _hE hb ha _hface hr₁ hr₂ hr₃ hr₄ hactive
  apply PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab ?_ hactive.le
  refine ⟨⟨⟨hsum, hb, ha, hinfo, hr₁, ?_⟩, hr₂, hr₃⟩, hr₄⟩
  intro hq
  exact PsiCompactAnalytic.active_bias_lt_eight_entropy μ hq hactive.le

end GeneralCK.PsiSeventhBias

namespace GeneralCK

structure ResidualPsiSeventhBiasRemainingOwners : Prop where
  sameChart : SameSidePsiExtendedChartOwner
  oppositeCentral : PsiSeventhBias.CentralOwner
  oppositeCompact : PsiSeventhBias.CompactOwner

theorem ResidualPsiSeventhBiasRemainingOwners.toEighthBias
    (h : ResidualPsiSeventhBiasRemainingOwners) : ResidualPsiEighthBiasRemainingOwners where
  sameChart := h.sameChart
  oppositeCentral := PsiSeventhBias.toEighthCentralOwner h.oppositeCentral
  oppositeCompact := PsiSeventhBias.toEighthCompactOwner h.oppositeCompact

theorem generalCourtadeKumar_of_seventh_bias_remaining_owners
    (hphi : CanonicalUnbalancedPhiOwner) (hpsi : ResidualPsiSeventhBiasRemainingOwners) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_eighth_bias_remaining_owners hphi hpsi.toEighthBias

end GeneralCK

#print axioms GeneralCK.PsiSeventhBias.logarithmic_eight_comparison
#print axioms GeneralCK.PsiSeventhBias.parent_dominance_ratio8
#print axioms GeneralCK.PsiSeventhBias.active_bias_lt_eight_entropy
#print axioms GeneralCK.PsiSeventhBias.endpoint_coefficient_lower
#print axioms GeneralCK.PsiSeventhBias.split_loss_upper
#print axioms GeneralCK.PsiSeventhBias.objective_lower_bound
#print axioms GeneralCK.PsiSeventhBias.signed_split_lower
#print axioms GeneralCK.PsiSeventhBias.parent_physical
#print axioms GeneralCK.PsiSeventhBias.parent_gain_budget
#print axioms GeneralCK.PsiSeventhBias.retained_child_margin
#print axioms GeneralCK.PsiSeventhBias.law_gap_margin
#print axioms GeneralCK.PsiSeventhBias.law_gap_le_cost
#print axioms GeneralCK.PsiSeventhBias.toEighthCompactOwner
#print axioms GeneralCK.PsiSeventhBias.compactOwner_of_affineCertificate
#print axioms GeneralCK.PsiSeventhBias.toEighthCentralOwner
#print axioms GeneralCK.PsiSeventhBias.centralOwner_of_affineCertificate
#print axioms GeneralCK.ResidualPsiSeventhBiasRemainingOwners.toEighthBias
#print axioms GeneralCK.generalCourtadeKumar_of_seventh_bias_remaining_owners

end


