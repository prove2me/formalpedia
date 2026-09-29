-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerRegularContact
-- name    : CK_GeneralCK_CorrectionHighUNearCornerRegularContact
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:21:42.85079+00:00
-- url     : https://prove2.me/theorems/f50dd8d7-8bb0-423d-9b8a-21d097986567
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHighUNearCornerRegularContact` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHighUNearCornerRegularContact` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHighUNearCornerRegularContact` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHighUNearCornerRegularContact (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHighUNearCornerRegularContact.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerContactRemainder

/-!
# Removing the gap division from the normalized correction contact

`regularContactRatio` equals `Natural.contact u w / (w-u)` at interior
points and remains continuous when the gap is zero. Its diagonal value is
exactly `1 / H u`. This removes only the contact's gap factor: no analogous
divisibility or face theorem for `Natural.m11` or `Natural.kdet` is claimed.
-/

namespace GeneralCK.Correction.HighU

open Certificates.Reflection

noncomputable def regularContactRatio (u w : ℝ) : ℝ :=
  2 * biasE (Reflection.regularContact (2 * (w - u) / Natural.entropySum u w)) /
    Natural.entropySum u w

theorem contact_eq_regularContact
    {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1 / 2) :
    Natural.contact u w =
      Reflection.regularContact (2 * (w - u) / Natural.entropySum u w) := by
  have hS : 0 < Natural.entropySum u w := by
    unfold Natural.entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    exact add_pos (mul_pos (H_pos hu (by linarith)) log_two_pos)
      (mul_pos (H_pos (hu.trans huw) (by linarith)) log_two_pos)
  rw [Reflection.regularContact_pos_eq (div_pos (by linarith) hS), inv_div]
  rfl

theorem regularContactRatio_eq_contact_div_gap
    {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1 / 2) :
    regularContactRatio u w = Natural.contact u w / (w - u) := by
  have hd : 0 < w - u := sub_pos.mpr huw
  have hS : 0 < Natural.entropySum u w := by
    unfold Natural.entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    exact add_pos (mul_pos (H_pos hu (by linarith)) log_two_pos)
      (mul_pos (H_pos (hu.trans huw) (by linarith)) log_two_pos)
  have hc := Natural.contact_spec hu huw hw
  have hE := Reflection.biasE_pos_wide (by linarith [hc.1]) hc.2.1
  have heq := (div_eq_div_iff hE.ne' hS.ne').mp hc.2.2
  unfold regularContactRatio
  rw [← contact_eq_regularContact hu huw hw]
  apply (div_eq_div_iff hS.ne' hd.ne').2
  nlinarith only [heq]

theorem regularContactRatio_diagonal (u : ℝ) :
    regularContactRatio u u = 1 / H u := by
  simp only [regularContactRatio, sub_self, mul_zero, zero_div,
    Reflection.regularContact_zero, biasE, add_zero, sub_zero,
    Real.log_one, mul_zero, zero_div, Natural.entropySum,
    Certificates.Mixed.hn_eq_H_mul_log]
  by_cases hH : H u = 0
  · simp [hH]
  · field_simp [hH, log_two_pos.ne']
    norm_num

theorem continuousAt_regularContactRatio {u w : ℝ}
    (hS : Natural.entropySum u w ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => regularContactRatio p.1 p.2) (u, w) := by
  have hSc : Continuous (fun p : ℝ × ℝ => Natural.entropySum p.1 p.2) := by
    simp_rw [Natural.entropySum, Certificates.Mixed.hn_eq_H_mul_log]
    exact ((H_continuous.comp continuous_fst).mul_const (Real.log 2)).add
      ((H_continuous.comp continuous_snd).mul_const (Real.log 2))
  have ht : ContinuousAt
      (fun p : ℝ × ℝ => 2 * (p.2 - p.1) / Natural.entropySum p.1 p.2) (u, w) :=
    ((continuous_snd.sub continuous_fst).const_mul 2).continuousAt.div
      hSc.continuousAt hS
  have hc := Reflection.regularContact_mem (2 * (w - u) / Natural.entropySum u w)
  have hcc : ContinuousAt
      (fun p : ℝ × ℝ => Reflection.regularContact
        (2 * (p.2 - p.1) / Natural.entropySum p.1 p.2)) (u, w) :=
    (Reflection.continuousAt_regularContact _).comp
      (f := fun p : ℝ × ℝ => 2 * (p.2 - p.1) / Natural.entropySum p.1 p.2) ht
  have he := (Reflection.hasDerivAt_biasE hc.1 hc.2).continuousAt.comp
    (f := fun p : ℝ × ℝ => Reflection.regularContact
      (2 * (p.2 - p.1) / Natural.entropySum p.1 p.2)) hcc
  exact (he.const_mul 2).div hSc.continuousAt hS

noncomputable def nearCornerRegularContactRatio (t rho : ℝ) : ℝ :=
  regularContactRatio (1 / 2 - t) (1 / 2 - (1 - rho) * t)

theorem nearCornerRegularContactRatio_zero_t (rho : ℝ) :
    nearCornerRegularContactRatio 0 rho = 1 := by
  simp only [nearCornerRegularContactRatio, sub_zero, mul_zero,
    regularContactRatio_diagonal, H_half, div_one]

theorem nearCornerRegularContactRatio_zero_rho (t : ℝ) :
    nearCornerRegularContactRatio t 0 = 1 / H (1 / 2 - t) := by
  simp only [nearCornerRegularContactRatio, sub_zero, one_mul,
    regularContactRatio_diagonal]

/-- Continuity on both zero-coordinate faces, including their intersection. -/
theorem continuousAt_nearCornerRegularContactRatio
    {t rho : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 100)
    (hr : 0 ≤ rho) (hr1 : rho ≤ 1 / 100) :
    ContinuousAt (fun p : ℝ × ℝ => nearCornerRegularContactRatio p.1 p.2) (t, rho) := by
  have hu0 : 0 < (1 / 2 : ℝ) - t := by linarith
  have hu1 : (1 / 2 : ℝ) - t < 1 := by linarith
  have hw0 : 0 < (1 / 2 : ℝ) - (1 - rho) * t := by
    nlinarith only [mul_nonneg hr ht, ht1]
  have hw1 : (1 / 2 : ℝ) - (1 - rho) * t < 1 := by
    nlinarith only [mul_nonneg (show 0 ≤ 1 - rho by linarith) ht]
  have hS : Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - rho) * t) ≠ 0 := by
    apply ne_of_gt
    unfold Natural.entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    exact add_pos (mul_pos (H_pos hu0 hu1) log_two_pos)
      (mul_pos (H_pos hw0 hw1) log_two_pos)
  have hcoord : Continuous
      (fun p : ℝ × ℝ => ((1 / 2 : ℝ) - p.1, 1 / 2 - (1 - p.2) * p.1)) :=
    (continuous_const.sub continuous_fst).prodMk
      (continuous_const.sub ((continuous_const.sub continuous_snd).mul continuous_fst))
  exact (continuousAt_regularContactRatio hS).comp
    (x := (t, rho))
    (f := fun p : ℝ × ℝ => ((1 / 2 : ℝ) - p.1, 1 / 2 - (1 - p.2) * p.1))
    hcoord.continuousAt

theorem nearCornerRegularContactRatio_eq
    {t rho : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    nearCornerRegularContactRatio t rho =
      Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t) / (rho * t) := by
  have hu0 : 0 < (1 / 2 : ℝ) - t := by linarith
  have huw : (1 / 2 : ℝ) - t < 1 / 2 - (1 - rho) * t := by
    nlinarith only [mul_pos hr ht]
  have hw : (1 / 2 : ℝ) - (1 - rho) * t < 1 / 2 := by
    nlinarith only [mul_pos (show 0 < 1 - rho by linarith) ht]
  unfold nearCornerRegularContactRatio
  rw [regularContactRatio_eq_contact_div_gap hu0 huw hw]
  congr 1
  ring

/-- A uniform quadratic enclosure for the extension on the entire closed
near-corner rectangle, including the zero-gap face. -/
theorem nearCornerRegularContactRatio_closed_remainder
    {t rho : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 100)
    (hr : 0 ≤ rho) (hr1 : rho ≤ 1 / 100) :
    0 ≤ nearCornerRegularContactRatio t rho - 1 ∧
      nearCornerRegularContactRatio t rho - 1 ≤ 5 * t ^ 2 := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simp only [nearCornerRegularContactRatio_zero_t, sub_self, zero_pow (by decide : 2 ≠ 0),
      mul_zero, le_refl, and_self]
  rcases hr.eq_or_lt with hr | hr
  · subst rho
    rw [nearCornerRegularContactRatio_zero_rho]
    have hu0 : 0 < (1 / 2 : ℝ) - t := by linarith
    have hu1 : (1 / 2 : ℝ) - t < 1 / 2 := by linarith
    have hH0 : 0 < H (1 / 2 - t) := H_pos hu0 (by linarith)
    have hH1 := H_le_one (1 / 2 - t)
    have hpar : 1 - 4 * t ^ 2 ≤ H (1 / 2 - t) := by
      have hp := H_gt_parabola hu0 hu1
      nlinarith only [hp]
    constructor
    · have hl : (1 : ℝ) ≤ 1 / H (1 / 2 - t) := (le_div_iff₀ hH0).2 (by simpa using hH1)
      linarith
    · have ht2 : t ^ 2 ≤ (1 / 10000 : ℝ) := by nlinarith [ht1]
      have hprod := mul_le_mul_of_nonneg_left hpar (show 0 ≤ 5 * t ^ 2 + 1 by positivity)
      have hsmall := mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - 20 * t ^ 2 by linarith)
      have hu : 1 / H (1 / 2 - t) ≤ 5 * t ^ 2 + 1 := (div_le_iff₀ hH0).2 (by
        nlinarith only [hprod, hsmall])
      linarith
  · rw [nearCornerRegularContactRatio_eq ht ht1 hr hr1]
    have h := nearCorner_contact_ratio_remainder ht ht1 hr hr1
    exact ⟨h.1.le, h.2.le⟩

#print axioms contact_eq_regularContact
#print axioms regularContactRatio_eq_contact_div_gap
#print axioms regularContactRatio_diagonal
#print axioms continuousAt_regularContactRatio
#print axioms nearCornerRegularContactRatio_zero_t
#print axioms nearCornerRegularContactRatio_zero_rho
#print axioms continuousAt_nearCornerRegularContactRatio
#print axioms nearCornerRegularContactRatio_eq
#print axioms nearCornerRegularContactRatio_closed_remainder

end GeneralCK.Correction.HighU


