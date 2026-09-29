-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerRadialBounds
-- name    : CK_GeneralCK_CorrectionHighUNearCornerRadialBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T05:59:54.429992+00:00
-- url     : https://prove2.me/theorems/26a7f097-6524-4fae-9a26-a4251002e0a2
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHighUNearCornerRadialBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHighUNearCornerRadialBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHighUNearCornerRadialBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHighUNearCornerRadialBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHighUNearCornerRadialBounds.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerEntropyBounds

/-! Elementary radial slope and weight estimates for the high-u corner. -/

namespace GeneralCK.Correction.HighU

open Certificates.Reflection

private theorem corner_biasB_lower {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) :
    Real.log 2 ≤ biasB c := by
  have hl := Real.log_nonpos (show 0 ≤ 1 - c * c by nlinarith)
    (show 1 - c * c ≤ 1 by nlinarith)
  unfold biasB
  linarith

/-- A cubic lower estimate for the natural radial slope. -/
theorem nearCorner_Fs_lower {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1 / 100) :
    4 * c - 4 * c ^ 3 ≤ Natural.Fs c := by
  have hcwide : c < 1 := by linarith
  have hg : 0 < 1 - c ^ 2 := by nlinarith
  have hcsq : c ^ 2 ≤ (1 / 10000 : ℝ) := by nlinarith
  have hB := corner_biasB_lower hc hcwide
  have hBrat : (69 / 100 : ℝ) ≤ biasB c := nearCorner_log_two_lower.trans hB
  have hB0 : 0 < biasB c := by linarith
  have hE0 : 0 ≤ biasE c :=
    (Reflection.biasE_pos_wide (by linarith) hcwide).le
  have hBg : 1 ≤ 2 * (1 - c ^ 2) * biasB c := by
    have hp := mul_le_mul_of_nonneg_right hBrat hg.le
    nlinarith only [hp, hcsq]
  have hA : SmallMean.A c ≤ 2 * c * biasB c := by
    apply (SmallMean.A_upper hc hcwide).trans
    apply (div_le_iff₀ hg).2
    have hp := mul_le_mul_of_nonneg_left hBg hc
    nlinarith only [hp]
  have hE : (1 - 2 * c ^ 2) * biasB c ≤ biasE c := by
    have heq := Reflection.biasB_eq_biasE_add (by linarith : -1 < c) hcwide
    have hp := mul_le_mul_of_nonneg_left hA hc
    nlinarith only [heq, hp]
  have hElow : 2 * c * (1 - 2 * c ^ 2) ≤ 2 * biasE c * c / biasB c := by
    apply (le_div_iff₀ hB0).2
    have hp := mul_le_mul_of_nonneg_left hE (show 0 ≤ 2 * c by positivity)
    nlinarith only [hp]
  have hdiv : 2 * biasE c * c / biasB c ≤
      2 * biasE c * c / ((1 - c ^ 2) * biasB c) := by
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos hg hB0)
    nlinarith [mul_nonneg (sq_nonneg c) hB0.le]
  have heq : Natural.Fs c = 2 * SmallMean.A c +
      2 * biasE c * c / ((1 - c ^ 2) * biasB c) := by
    unfold Natural.Fs
    field_simp [hg.ne', hB0.ne']
    <;> ring
  rw [heq]
  have hAlow := SmallMean.A_lower hc hcwide
  nlinarith only [hAlow, hElow, hdiv]

/-- The physical contact version of the radial cubic estimate. -/
theorem nearCorner_Fs_contact_lower
    {t rho : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    4 * rho * t - 8 * rho ^ 3 * t ^ 3 ≤
      Natural.Fs (Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t)) := by
  let c := Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t)
  let d := rho * t
  have hd : 0 < d := mul_pos hr ht
  have hc := nearCorner_contact_lt_one_thousand_one ht ht1 hr hr1
  change 0 < c ∧ c < (1001 / 1000 : ℝ) * rho * t at hc
  have hc0 : 0 ≤ c := hc.1.le
  have hcd : c ≤ (1001 / 1000 : ℝ) * d := by
    dsimp [d]
    nlinarith only [hc.2]
  have hdc : d ≤ c := by
    have hl := (nearCorner_contact_cubic_remainder ht ht1 hr hr1).1
    change 0 < c - d at hl
    linarith
  have hdmax : d ≤ (1 / 10000 : ℝ) := by
    dsimp [d]
    have hp := mul_le_mul hr1 ht1 ht.le (by norm_num : (0 : ℝ) ≤ 1 / 100)
    norm_num at hp
    exact hp
  have hcsmall : c ≤ (1 / 100 : ℝ) := by nlinarith only [hcd, hdmax]
  have hcube : c ^ 3 ≤ 2 * d ^ 3 := by
    calc
      c ^ 3 ≤ ((1001 / 1000 : ℝ) * d) ^ 3 := by gcongr
      _ ≤ 2 * d ^ 3 := by nlinarith only [pow_nonneg hd.le 3]
  have hF := nearCorner_Fs_lower hc.1.le hcsmall
  change 4 * rho * t - 8 * rho ^ 3 * t ^ 3 ≤ Natural.Fs c
  dsimp [d] at hdc hcube
  nlinarith only [hF, hdc, hcube]

/-- Dropping the nonpositive numerator term gives a useful radial bound. -/
theorem nearCorner_weight_radial_upper {c S : ℝ}
    (hc : 0 ≤ c) (hc1 : c < 1) (hS : 0 < S) :
    2 * Natural.Fss c S ≤ 16 * Real.log 2 / (S * (1 - c ^ 2) ^ 2) := by
  have hg : 0 < 1 - c ^ 2 := by nlinarith
  have hE0 : 0 ≤ biasE c :=
    (Reflection.biasE_pos_wide (by linarith) hc1).le
  have hEL : biasE c ≤ Real.log 2 :=
    Reflection.biasE_le_log_two_wide (by linarith) hc1
  have hLB := corner_biasB_lower hc hc1
  have hB0 : 0 < biasB c := log_two_pos.trans_le hLB
  have hEB : biasE c ≤ biasB c := hEL.trans hLB
  have hcub : (biasE c) ^ 3 ≤ Real.log 2 * (biasB c) ^ 2 := by
    calc
      (biasE c) ^ 3 = biasE c * (biasE c) ^ 2 := by ring
      _ ≤ Real.log 2 * (biasB c) ^ 2 := by gcongr
  have hnum : 8 * ((biasE c) ^ 3 * (2 * biasB c - c ^ 2)) ≤
      16 * Real.log 2 * (biasB c) ^ 3 := by
    have hp := mul_le_mul_of_nonneg_right hcub (show 0 ≤ 2 * biasB c by positivity)
    have hn := mul_nonneg (pow_nonneg hE0 3) (sq_nonneg c)
    nlinarith only [hp, hn]
  have hinner : 8 * ((biasE c) ^ 3 * (2 * biasB c - c ^ 2)) / (biasB c) ^ 3 ≤
      16 * Real.log 2 := (div_le_iff₀ (pow_pos hB0 3)).2 hnum
  calc
    2 * Natural.Fss c S =
        (8 * ((biasE c) ^ 3 * (2 * biasB c - c ^ 2)) / (biasB c) ^ 3) /
          (S * (1 - c ^ 2) ^ 2) := by
      unfold Natural.Fss
      field_simp [hg.ne', hB0.ne', hS.ne']
      <;> ring
    _ ≤ 16 * Real.log 2 / (S * (1 - c ^ 2) ^ 2) :=
      div_le_div_of_nonneg_right hinner (by positivity)

/-- The natural rank weight differs from its corner value by at most a
uniform quadratic error. -/
theorem nearCorner_weight_upper
    {t rho : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    Natural.weight (1 / 2 - t) (1 / 2 - (1 - rho) * t) ≤
      8 + (117 / 5 : ℝ) * t ^ 2 := by
  let c := Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t)
  let S := Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - rho) * t)
  have hc := nearCorner_contact_lt_one_thousand_one ht ht1 hr hr1
  change 0 < c ∧ c < (1001 / 1000 : ℝ) * rho * t at hc
  have hc0 : 0 ≤ c := hc.1.le
  have hct : c ≤ (1001 / 100000 : ℝ) * t := by
    have hp := mul_le_mul_of_nonneg_right hr1 ht.le
    nlinarith only [hc.2, hp]
  have hcsq : c ^ 2 ≤ t ^ 2 / 9000 := by
    have hp := mul_nonneg (sub_nonneg.mpr hct)
      (show 0 ≤ (1001 / 100000 : ℝ) * t + c by positivity)
    nlinarith only [hp, sq_nonneg t]
  have htsq : t ^ 2 ≤ (1 / 10000 : ℝ) := by nlinarith only [ht.le, ht1]
  have hc1 : c < 1 := by nlinarith only [hcsq, htsq, sq_nonneg (c - 1)]
  have hSenc := nearCorner_entropySum_enclosure ht.le ht1 hr.le hr1
  change 2 * Real.log 2 - (2001 / 500 : ℝ) * t ^ 2 ≤ S ∧ S ≤ 2 * Real.log 2 at hSenc
  have hL := nearCorner_log_two_lower
  have hL1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hS0 : 0 < S := by nlinarith only [hSenc.1, hL, htsq]
  have hS2 : S ≤ 2 := by linarith [hSenc.2]
  have hg : 0 < 1 - c ^ 2 := by nlinarith only [hcsq, htsq]
  have hden : 2 * Real.log 2 - (4003 / 1000 : ℝ) * t ^ 2 ≤
      S * (1 - c ^ 2) ^ 2 := by
    have hp := mul_le_mul_of_nonneg_right hS2 (sq_nonneg c)
    have hn := mul_nonneg hS0.le (sq_nonneg (c ^ 2))
    nlinarith only [hSenc.1, hp, hn, hcsq, sq_nonneg t]
  have hscalar : 16 * Real.log 2 ≤
      (8 + (117 / 5 : ℝ) * t ^ 2) *
        (2 * Real.log 2 - (4003 / 1000 : ℝ) * t ^ 2) := by
    have hk : 0 ≤ (234 / 5 : ℝ) * Real.log 2 - 4003 / 125 -
        (468351 / 5000 : ℝ) * t ^ 2 := by nlinarith only [hL, htsq]
    have hp := mul_nonneg (sq_nonneg t) hk
    nlinarith only [hp]
  have hfinal : 16 * Real.log 2 / (S * (1 - c ^ 2) ^ 2) ≤
      8 + (117 / 5 : ℝ) * t ^ 2 := by
    apply (div_le_iff₀ (show 0 < S * (1 - c ^ 2) ^ 2 by positivity)).2
    have hp := mul_le_mul_of_nonneg_left hden
      (show 0 ≤ 8 + (117 / 5 : ℝ) * t ^ 2 by positivity)
    exact hscalar.trans hp
  exact (nearCorner_weight_radial_upper hc.1.le hc1 hS0).trans hfinal

#print axioms nearCorner_Fs_lower
#print axioms nearCorner_Fs_contact_lower
#print axioms nearCorner_weight_radial_upper
#print axioms nearCorner_weight_upper

end GeneralCK.Correction.HighU


