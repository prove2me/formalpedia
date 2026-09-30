-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEighthBiasClosure
-- name    : CK_GeneralCK_PsiEighthBiasClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:07:27.387207+00:00
-- url     : https://prove2.me/theorems/1325682f-dae9-49d6-8d82-86669c63a5b3
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEighthBiasClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEighthBiasClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEighthBiasClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEighthBiasClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEighthBiasClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiEntropy200Closure

-- ===== source module GeneralCK.PsiEighthBiasClosure =====
section

/-!
# Retained-child endpoint closure through parent bias one eighth

The signed split keeps the two actual child profiles. Three entropy bands
extend the existing bias-one-tenth wedge to bias one eighth, with all closed
faces assigned to the proved law-level owner.
-/

namespace GeneralCK.PsiEighthBias
open PsiChildEntropyCoupling PsiSignedSplit

theorem capacity_quadratic_half {z : ℝ} (hz : 0 ≤ z) (hzu : z ≤ 1 / 2) :
    capacity z ≤ (19 / 36) * z ^ 2 := by
  have hz1 : z < 1 := by linarith
  rw [capacity_eq_Cn (by rw [abs_of_nonneg hz]; exact hz1)]
  have hs : z ^ 2 ≤ 1 / 4 := by nlinarith
  have hn : 0 < 1 - z ^ 2 := by nlinarith
  have hf : z ^ 2 / (12 * (1 - z ^ 2)) ≤ (1 / 36 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - z ^ 2))).mpr
    nlinarith only [hs]
  have h := LowInformation.Cn_upper_sharp hz hz1
  have hh := mul_le_mul_of_nonneg_left hf (sq_nonneg z)
  have he : z ^ 2 * (z ^ 2 / (12 * (1 - z ^ 2))) =
      z ^ 4 / (12 * (1 - z ^ 2)) := by ring
  rw [he] at hh
  linarith

theorem split_loss_le_four_sq {c q : ℝ} (hc : 1 / 3 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 8) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ 4 * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (1 / 3 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (1 / 3 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  rw [show (13 * q / 6) / (2 * (1 / 3 : ℝ)) = 13 * q / 4 by ring] at h
  have hb := capacity_quadratic_half (z := 13 * q / 4) (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

theorem objective_ge_neg_four_sq {c q t : ℝ} (hc : 1 / 3 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 8) (ht : |t| < 1) :
    -(4 * q ^ 2) ≤ objective c (13 * q / 6) t := by
  have hcpos : 0 < c := by linarith
  have hk : |13 * q / 6| < 2 * c := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  obtain ⟨hz, _, _⟩ := objective_minimum hcpos hk
  have h := objective_lower hcpos.le hz ht
  rw [mul_div_cancel₀ _ (show 2 * c ≠ 0 by positivity)] at h
  linarith [split_loss_le_four_sq hc hq hqu]

theorem signed_split_ge_neg_four_sq {c q E A t : ℝ}
    (hc : 1 / 3 ≤ c) (hq : 0 ≤ q) (hqu : q ≤ 1 / 8)
    (hE : 0 < E) (hA : 0 ≤ A) (hAu : A ≤ 13 * q / (3 * E)) (ht : |t| < 1) :
    -(4 * q ^ 2) ≤ c * barrier t + E * t * A / 2 + (13 * q / 6) * (tilt t - t) := by
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
    have hobj := objective_ge_neg_four_sq (t := -t) hc hq hqu (by simpa using ht)
    unfold objective at hobj
    rw [barrier_neg, tilt_neg] at hobj
    nlinarith

theorem parent_physical {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 8) :
    E + (1 - H ((1 - q) / 2)) ≤ 1 := by
  rcases hq.eq_or_lt with he | hp
  · rw [← he]
    norm_num [H_half]
    linarith
  · have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
    have hs := mul_nonneg hq (show 0 ≤ 1 / 8 - q by linarith)
    nlinarith

/-- A reusable rational parent gain from a bound on q²/E. -/
theorem parent_gain_of_sq_bound {E q K D : ℝ}
    (hE : 0 < E) (hEu : E ≤ 11 / 200) (hq : 0 ≤ q) (hqu : q ≤ 1 / 8)
    (hsq : q ^ 2 ≤ K * E) (hcoef : 49 / 50 + (7 / 10) * K ≤ D) :
    (1 / D) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hg := PsiLargerEntropyRedesign.parent_gain_rational hE hq (by linarith)
    (parent_physical hE hEu hq hqu)
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have hh := Certificates.PilotData.log_two.2
    norm_num at hh
    linarith
  have hLsq : (Real.log 2) ^ 2 ≤ (49 / 100 : ℝ) := by nlinarith [log_two_pos]
  have hden : Real.log 2 * (2 * Real.log 2 * E + q ^ 2) ≤ D * E := by
    have h1 := mul_le_mul_of_nonneg_right hLsq hE.le
    have h2 := mul_le_mul hL hsq (sq_nonneg q) (by norm_num : (0 : ℝ) ≤ 7 / 10)
    have h3 := mul_le_mul_of_nonneg_right hcoef hE.le
    nlinarith only [h1, h2, h3]
  have hb := div_le_div_of_nonneg_left (sq_nonneg q)
    (by positivity : 0 < Real.log 2 * (2 * Real.log 2 * E + q ^ 2)) hden
  have he : q ^ 2 / (D * E) = (1 / D) * (q ^ 2 / E) := by ring
  rw [he] at hb
  exact hb.trans hg

/-- Three entropy bands preserve enough gain to pay the whole signed loss. -/
theorem parent_gain_budget {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 11 / 200)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 8) (hqE : q ≤ 8 * E) :
    (1 / 2 + 4 * E + 1 / 100) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hs := mul_nonneg hq (show 0 ≤ 1 / 8 - q by linarith)
  have hsq : q ^ 2 ≤ 1 / 64 := by nlinarith
  have hn : 0 ≤ q ^ 2 / E := by positivity
  by_cases hlow : E ≤ 1 / 50
  · have hqSq : q ^ 2 ≤ 1 * E := by nlinarith only [hs, hqE]
    have hg := parent_gain_of_sq_bound (K := 1) (D := 42 / 25)
      hE hEu hq hqu hqSq (by norm_num)
    have hm := mul_le_mul_of_nonneg_right
      (show 1 / 2 + 4 * E + 1 / 100 ≤ (1 : ℝ) / (42 / 25) by linarith) hn
    exact hm.trans hg
  · by_cases hmid : E ≤ 1 / 32
    · have hqSq : q ^ 2 ≤ (25 / 32) * E := by linarith [lt_of_not_ge hlow]
      have hg := parent_gain_of_sq_bound (K := 25 / 32) (D := 20 / 13)
        hE hEu hq hqu hqSq (by norm_num)
      have hm := mul_le_mul_of_nonneg_right
        (show 1 / 2 + 4 * E + 1 / 100 ≤ (1 : ℝ) / (20 / 13) by linarith) hn
      exact hm.trans hg
    · have hqSq : q ^ 2 ≤ (1 / 2) * E := by linarith [lt_of_not_ge hmid]
      have hg := parent_gain_of_sq_bound (K := 1 / 2) (D := 4 / 3)
        hE hEu hq hqu hqSq (by norm_num)
      have hm := mul_le_mul_of_nonneg_right
        (show 1 / 2 + 4 * E + 1 / 100 ≤ (1 : ℝ) / (4 / 3) by linarith) hn
      exact hm.trans hg

theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEu : E ≤ 11 / 200) (hd : 8 * E ≤ d) (hdu : d ≤ 1)
    (hq : 0 ≤ q) (hqu : q ≤ 1 / 8) (hqE : q ≤ 8 * E) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 100) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
  have hqd : q ≤ d := hqE.trans hd
  have hg := parent_gain_budget hE hEu hq hqu hqE
  have hr := PsiRadialDeficit.radial_average_loss_le_half hE hd q
  rw [abs_of_nonneg (show 0 ≤ d - q by linarith),
    abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
  have hr' : radialLoss d q E ≤ (q ^ 2 / E) / 2 := by
    rw [show q ^ 2 / (2 * E) = (q ^ 2 / E) / 2 by ring] at hr
    unfold radialLoss
    linarith only [hr]
  obtain ⟨hA, hAu⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq hqd
  have hc : 1 / 3 ≤ endpointCoefficient d := endpoint_coefficient_ge_third (by linarith) hdu
  have hs := signed_split_ge_neg_four_sq hc hq hqu hE hA hAu ht
  have hdec := retained_child_decomposition (C := 1 - H ((1 - q) / 2)) hq hqd hE hEu ht
  have he : (1 / 2 + 4 * E + 1 / 100) * (q ^ 2 / E) =
      (1 / 2 + 1 / 100) * (q ^ 2 / E) + 4 * q ^ 2 := by
    field_simp
    ring
  rw [he] at hg
  linarith only [hg, hr', hs, hdec]

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEu : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 8)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hqE := PsiCompactAnalytic.active_bias_lt_eight_entropy μ hq hactive
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hm := retained_child_margin (d := μ.b - μ.a) (q := 1 - μ.a - μ.b)
    (E := μ.meanEntropy) (t := (μ.e - μ.f) / (μ.e + μ.f)) hE hEu hd
    (by linarith [μ.a_interior.1, μ.b_interior.2]) (by linarith) hq hqE.le ht
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
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 8)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hh := law_gap_margin μ hsum hEu hd hq hactive
  have hn : 0 ≤ (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [hh, hn]

def compactRegion (a b E : ℝ) : Prop :=
  PsiEntropy200.compactRegion a b E ∧ (1 - a - b ≤ 1 / 8 → 11 / 200 < E)

def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toEntropy200CompactOwner (h : CompactOwner) : PsiEntropy200.CompactOwner := by
  intro k μ hregion hactive
  by_cases hw : 1 - μ.a - μ.b ≤ 1 / 8 ∧ μ.meanEntropy ≤ 11 / 200
  · exact law_gap_le_cost μ hregion.1.1.le hw.2
      (by linarith [hregion.1.2.2.2.1]) hw.1 hactive.le
  · apply h k μ ⟨hregion, ?_⟩ hactive
    intro hq
    by_contra hn
    exact hw ⟨hq, le_of_not_gt hn⟩

/-- The remaining compact certificate still retains both hybrid children
and minimizes only over the exact feasible entropy allocation interval. -/
theorem compactOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate compactRegion) : CompactOwner := by
  intro k μ hregion hactive
  have hab : μ.a < μ.b := by
    linarith [hregion.1.1.2.1, hregion.1.1.2.2.2.1]
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

def centralRemainder (a b E : ℝ) : Prop :=
  11 / 200 < E ∨ b - a < 8 * E ∨ 1 / 8 < 1 - a - b

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy → 1 / 2 ≤ μ.b → 1 / 10 ≤ μ.a →
    (μ.a ≤ 1 / 10 → 1 / 32768 < μ.meanEntropy) →
    PsiCentralAnalytic.centralRemainder μ.a μ.b μ.meanEntropy →
    PsiEntropy200.centralRemainder μ.a μ.b μ.meanEntropy →
    centralRemainder μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toEntropy200CentralOwner (h : CentralOwner) : PsiEntropy200.CentralOwner := by
  intro k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hactive
  by_cases hw : μ.meanEntropy ≤ 11 / 200 ∧ 8 * μ.meanEntropy ≤ μ.b - μ.a ∧
      1 - μ.a - μ.b ≤ 1 / 8
  · exact law_gap_le_cost μ hsum.le hw.1 hw.2.1 hw.2.2 hactive.le
  · apply h k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ ?_ hactive
    by_contra hn
    change ¬ (11 / 200 < μ.meanEntropy ∨ μ.b - μ.a < 8 * μ.meanEntropy ∨
      1 / 8 < 1 - μ.a - μ.b) at hn
    push Not at hn
    exact hw hn

/-- A three-variable certificate region containing the remaining central chart. -/
def centralRegion (a b E : ℝ) : Prop :=
  PsiCentralAnalytic.centralRegion a b E ∧
    PsiEntropy200.centralRemainder a b E ∧ centralRemainder a b E

theorem centralOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate centralRegion) : CentralOwner := by
  intro k μ hab hsum _hmean hinfo _hE hb ha _hface hr₁ hr₂ hr₃ hactive
  apply PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab ?_ hactive.le
  refine ⟨⟨hsum, hb, ha, hinfo, hr₁, ?_⟩, hr₂, hr₃⟩
  intro hq
  exact PsiCompactAnalytic.active_bias_lt_eight_entropy μ hq hactive.le

end GeneralCK.PsiEighthBias

namespace GeneralCK

/-- Only the opposite compact and central fields are narrowed here. -/
structure ResidualPsiEighthBiasRemainingOwners : Prop where
  sameChart : SameSidePsiExtendedChartOwner
  oppositeCentral : PsiEighthBias.CentralOwner
  oppositeCompact : PsiEighthBias.CompactOwner

theorem ResidualPsiEighthBiasRemainingOwners.toEntropy200
    (h : ResidualPsiEighthBiasRemainingOwners) : ResidualPsiEntropy200RemainingOwners where
  sameChart := h.sameChart
  oppositeCentral := PsiEighthBias.toEntropy200CentralOwner h.oppositeCentral
  oppositeCompact := PsiEighthBias.toEntropy200CompactOwner h.oppositeCompact

theorem generalCourtadeKumar_of_eighth_bias_remaining_owners
    (hphi : CanonicalUnbalancedPhiOwner) (hpsi : ResidualPsiEighthBiasRemainingOwners) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_entropy200_remaining_owners hphi hpsi.toEntropy200

end GeneralCK

#print axioms GeneralCK.PsiEighthBias.capacity_quadratic_half
#print axioms GeneralCK.PsiEighthBias.split_loss_le_four_sq
#print axioms GeneralCK.PsiEighthBias.objective_ge_neg_four_sq
#print axioms GeneralCK.PsiEighthBias.signed_split_ge_neg_four_sq
#print axioms GeneralCK.PsiEighthBias.parent_physical
#print axioms GeneralCK.PsiEighthBias.parent_gain_of_sq_bound
#print axioms GeneralCK.PsiEighthBias.parent_gain_budget
#print axioms GeneralCK.PsiEighthBias.retained_child_margin
#print axioms GeneralCK.PsiEighthBias.law_gap_margin
#print axioms GeneralCK.PsiEighthBias.law_gap_le_cost
#print axioms GeneralCK.PsiEighthBias.toEntropy200CompactOwner
#print axioms GeneralCK.PsiEighthBias.compactOwner_of_affineCertificate
#print axioms GeneralCK.PsiEighthBias.toEntropy200CentralOwner
#print axioms GeneralCK.PsiEighthBias.centralOwner_of_affineCertificate
#print axioms GeneralCK.ResidualPsiEighthBiasRemainingOwners.toEntropy200
#print axioms GeneralCK.generalCourtadeKumar_of_eighth_bias_remaining_owners

end


