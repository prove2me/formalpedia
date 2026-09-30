-- Prove2me | Definitions.Def_CK_GeneralCK_PsiFifthBiasAutomaticClosure
-- name    : CK_GeneralCK_PsiFifthBiasAutomaticClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:11:21.354336+00:00
-- url     : https://prove2.me/theorems/df18ae16-10af-467b-a13e-9dc2d98d73c2
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiFifthBiasAutomaticClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiFifthBiasAutomaticClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiFifthBiasAutomaticClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiFifthBiasAutomaticClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiFifthBiasAutomaticClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiParentFiveGain

-- ===== source module GeneralCK.PsiFifthBiasAutomaticClosure =====
section

/-! Automatic ratio-eight clipping through bias one fifth. -/

namespace GeneralCK.PsiFifthBiasAutomatic
open Set

theorem log_three_halves_lt_five_twelfths : Real.log (3 / 2 : ℝ) < 5 / 12 := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3 / 2)
    (show (3 / 2 : ℝ) < (25 / 24) ^ (10 : ℕ) by norm_num)
  rw [Real.log_pow] at h
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 25 / 24)
  norm_num at hu
  linarith only [h, hu]

theorem logarithmic_eight_comparison {x : ℝ} (hx : 8 ≤ x) :
    2 * Real.log x < 5 * Real.log (1 + 18 * x / 125) + 5 / 12 := by
  have hy : 0 ≤ x - 8 := by linarith
  have he : (3 / 2 : ℝ) * (1 + 18 * x / 125) ^ 5 - x ^ 2 =
      (2834352 / 30517578125) * (x - 8) ^ 5 +
      (42357816 / 6103515625) * (x - 8) ^ 4 +
      (1266028056 / 6103515625) * (x - 8) ^ 3 +
      (12816570323 / 6103515625) * (x - 8) ^ 2 +
      (43718836667 / 6103515625) * (x - 8) + 319294257047 / 61035156250 := by ring
  have hp : 0 < (3 / 2 : ℝ) * (1 + 18 * x / 125) ^ 5 - x ^ 2 := by rw [he]; positivity
  have hh := Real.log_lt_log (by positivity : 0 < x ^ 2)
    (show x ^ 2 < (3 / 2 : ℝ) * (1 + 18 * x / 125) ^ 5 by linarith)
  rw [Real.log_pow, Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0)
    (by positivity : (1 + 18 * x / 125) ^ 5 ≠ 0), Real.log_pow] at hh
  linarith only [hh, log_three_halves_lt_five_twelfths]

theorem parent_dominance_ratio8 {q E : ℝ} (hq : 0 < q) (hqu : q ≤ 1 / 5)
    (hE : 0 < E) (hr : 8 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  by_cases hsixth : q ≤ 1 / 6
  · exact PsiSixthBias.parent_dominance_ratio8 hq hsixth hE hr
  · let C := 1 - H ((1 - q) / 2)
    let x := q / E
    have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hr
    have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
    have hCupper : C ≤ q ^ 2 := by
      have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
      dsimp [C]
      nlinarith
    have hcap : E + C ≤ 13 / 200 := by
      have hs := mul_nonneg hq.le (show 0 ≤ 1 / 5 - q by linarith)
      nlinarith only [hr, hqu, hCupper, hs]
    have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
      have h := Certificates.PilotData.log_two.2
      norm_num at h
      linarith
    have hClower := SmallMean.Cn_ge_half_sq hq.le (show q ≤ 1 by linarith)
    change q ^ 2 / 2 ≤ Real.log 2 * C at hClower
    have hCrational : 18 * q ^ 2 / 25 ≤ C := by
      have hh := mul_le_mul_of_nonneg_right hL hC
      nlinarith only [hh, hClower]
    have hg := PsiParentFiveGain.eta_increment_ge_five_linear_log hE hC hcap
    have hl : Real.log (1 + 18 * q ^ 2 / (25 * E)) ≤ Real.log (1 + C / E) := by
      apply Real.log_le_log (by positivity)
      have hh := div_le_div_of_nonneg_right hCrational hE.le
      convert! add_le_add_left hh 1 using 1 <;> ring
    have hgm := mul_le_mul_of_nonneg_right hg log_two_pos.le
    have hid : (5 * C + Real.log (1 + C / E) / Real.log 2) * Real.log 2 =
        5 * C * Real.log 2 + Real.log (1 + C / E) := by field_simp
    rw [hid] at hgm
    have hF := (le_div_iff₀ log_two_pos).mp
      (PsiParentDominance.F_le_logarithmic_ratio8 hq hE hr)
    have hp := mul_lt_mul_of_pos_left (logarithmic_eight_comparison hx) hq
    have hs := strictConcaveOn_log_Ioi.concaveOn.2
      (show 0 < 1 + 18 * x / 125 by positivity)
      (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (show 0 ≤ 5 * q by positivity) (show 0 ≤ 1 - 5 * q by linarith)
      (show 5 * q + (1 - 5 * q) = 1 by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hs
    have hs' : 5 * q * Real.log (1 + 18 * x / 125) ≤
        Real.log (1 + 18 * q ^ 2 / (25 * E)) := by
      convert! hs using 1
      congr 1
      dsimp [x]
      ring
    have hlinear := mul_nonneg hq.le (show 0 ≤ q - 1 / 6 by linarith [lt_of_not_ge hsixth])
    have hcost : F q E < eta E - eta (E + C) := by
      apply (mul_lt_mul_iff_left₀ log_two_pos).mp
      change F q E * Real.log 2 ≤ 2 * q * Real.log x at hF
      nlinarith only [hF, hp, hs', hlinear, hl, hgm, hClower]
    unfold phi psi
    rw [show |1 - 2 * ((1 - q) / 2)| = q by
      rw [show 1 - 2 * ((1 - q) / 2) = q by ring, abs_of_pos hq]]
    have he : E + 1 - H ((1 - q) / 2) = E + C := by dsimp [C]; ring
    rw [he]
    linarith only [hcost]

theorem active_bias_lt_eight_entropy {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hq : 1 - μ.a - μ.b ≤ 1 / 5)
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

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEu : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 5)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost :=
  PsiFifthBias.law_gap_margin μ hsum hEu hd hq
    (active_bias_lt_eight_entropy μ hq hactive).le hactive

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEu : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 1 / 5)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost :=
  PsiFifthBias.law_gap_le_cost μ hsum hEu hd hq
    (active_bias_lt_eight_entropy μ hq hactive).le hactive

def compactRegion (a b E : ℝ) : Prop :=
  PsiFifthBias.compactRegion a b E ∧
    (1 - a - b ≤ 1 / 5 → 11 / 200 < E) ∧
    (1 - a - b ≤ 1 / 5 → 1 - a - b < 8 * E)

def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toFifthCompactOwner (h : CompactOwner) : PsiFifthBias.CompactOwner := by
  intro k μ hregion hactive
  have hclip : 1 - μ.a - μ.b ≤ 1 / 5 → 1 - μ.a - μ.b < 8 * μ.meanEntropy :=
    fun hq => active_bias_lt_eight_entropy μ hq hactive.le
  apply h k μ ⟨hregion, ?_, hclip⟩ hactive
  intro hq
  rcases hregion.2 hq with hE | hratio
  · exact hE
  · linarith [hclip hq]

theorem compactOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate compactRegion) : CompactOwner := by
  intro k μ hregion hactive
  have hold := hregion.1.1.1
  have hab : μ.a < μ.b := by
    linarith [hold.1.1.1.2.1, hold.1.1.1.2.2.2.1]
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

def centralRemainder (a b E : ℝ) : Prop :=
  (11 / 200 < E ∨ b - a < 8 * E ∨ 1 / 5 < 1 - a - b) ∧
    (1 - a - b ≤ 1 / 5 → 1 - a - b < 8 * E)

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
    centralRemainder μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toFifthCentralOwner (h : CentralOwner) : PsiFifthBias.CentralOwner := by
  intro k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hactive
  by_cases hw : μ.meanEntropy ≤ 11 / 200 ∧ 8 * μ.meanEntropy ≤ μ.b - μ.a ∧
      1 - μ.a - μ.b ≤ 1 / 5
  · exact law_gap_le_cost μ hsum.le hw.1 hw.2.1 hw.2.2 hactive.le
  · apply h k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ ⟨?_, ?_⟩ hactive
    · by_contra hn
      push Not at hn
      exact hw hn
    · intro hq
      exact active_bias_lt_eight_entropy μ hq hactive.le

def centralRegion (a b E : ℝ) : Prop :=
  PsiFifthBias.centralRegion a b E ∧ centralRemainder a b E

theorem centralOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate centralRegion) : CentralOwner := by
  intro k μ hab hsum _hmean hinfo _hE hb ha _hface hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇ hactive
  apply PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab ?_ hactive.le
  refine ⟨⟨⟨⟨⟨⟨hsum, hb, ha, hinfo, hr₁, ?_⟩, hr₂, hr₃⟩, hr₄⟩, hr₅⟩, hr₆⟩, hr₇⟩
  intro hq
  exact PsiCompactAnalytic.active_bias_lt_eight_entropy μ hq hactive.le

end GeneralCK.PsiFifthBiasAutomatic

namespace GeneralCK

/-- The exact residual active-psi owners after automatic ratio-eight clipping
through parent bias one fifth. -/
structure ResidualPsiFifthBiasAutomaticRemainingOwners : Prop where
  sameChart : SameSidePsiExtendedChartOwner
  oppositeCentral : PsiFifthBiasAutomatic.CentralOwner
  oppositeCompact : PsiFifthBiasAutomatic.CompactOwner

theorem ResidualPsiFifthBiasAutomaticRemainingOwners.toFifthBias
    (h : ResidualPsiFifthBiasAutomaticRemainingOwners) :
    ResidualPsiFifthBiasRemainingOwners where
  sameChart := h.sameChart
  oppositeCentral := PsiFifthBiasAutomatic.toFifthCentralOwner h.oppositeCentral
  oppositeCompact := PsiFifthBiasAutomatic.toFifthCompactOwner h.oppositeCompact

end GeneralCK

#print axioms GeneralCK.PsiFifthBiasAutomatic.log_three_halves_lt_five_twelfths
#print axioms GeneralCK.PsiFifthBiasAutomatic.logarithmic_eight_comparison
#print axioms GeneralCK.PsiFifthBiasAutomatic.parent_dominance_ratio8
#print axioms GeneralCK.PsiFifthBiasAutomatic.active_bias_lt_eight_entropy
#print axioms GeneralCK.PsiFifthBiasAutomatic.law_gap_margin
#print axioms GeneralCK.PsiFifthBiasAutomatic.law_gap_le_cost
#print axioms GeneralCK.PsiFifthBiasAutomatic.toFifthCompactOwner
#print axioms GeneralCK.PsiFifthBiasAutomatic.compactOwner_of_affineCertificate
#print axioms GeneralCK.PsiFifthBiasAutomatic.toFifthCentralOwner
#print axioms GeneralCK.PsiFifthBiasAutomatic.centralOwner_of_affineCertificate
#print axioms GeneralCK.ResidualPsiFifthBiasAutomaticRemainingOwners.toFifthBias

end


