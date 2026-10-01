-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarRadialContactJet
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarRadialContactJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:03:26.648237+00:00
-- url     : https://prove2.me/theorems/f2b48cc2-4661-4e9f-9ea4-4554544c3d96
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarRadialContactJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarRadialContactJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarRadialContactJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperHalfCollarRadialContactJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperHalfCollarRadialContactJet.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarMiddleEta

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperHalfCollarRadialContactJet =====
section

namespace GeneralCK

theorem leftUpper_halfEntropy_radial_data {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 64) :
    let h := (H (1 / 2 - z) + H (1 / 2 - w)) / 2
    (9 / 10 : ℝ) ≤ h ∧ h ≤ 1 ∧
      0 ≤ 1 - h ∧ 1 - h ≤ 4 * z ^ 2 ∧
      |1 - h - leftUpperHalfD2 z w (Real.log 2)| ≤ 3 * z ^ 4 := by
  let h := (H (1 / 2 - z) + H (1 / 2 - w)) / 2
  let D2 := leftUpperHalfD2 z w (Real.log 2)
  let D4 := leftUpperHalfD4 z w (Real.log 2)
  have hz := hw.trans hwz
  have hL : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hw2 : w ^ 2 ≤ z ^ 2 := by gcongr
  have hw4 : w ^ 4 ≤ z ^ 4 := by gcongr
  have hD2 : D2 ≤ 3 * z ^ 2 := by
    apply (div_le_iff₀ log_two_pos).2
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ 3 * z ^ 2 by positivity)]
  have hD40 : 0 ≤ D4 := by dsimp [D4, leftUpperHalfD4]; positivity
  have hD4 : D4 ≤ 2 * z ^ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * Real.log 2)).2
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ 6 * z ^ 4 by positivity)]
  have hz2 : z ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := by gcongr
  have hz4 : z ^ 4 ≤ z ^ 2 / 4096 := by
    nlinarith only [mul_le_mul_of_nonneg_right hz2 (sq_nonneg z)]
  have hz6 : z ^ 6 ≤ z ^ 4 / 4096 := by
    nlinarith only [mul_le_mul_of_nonneg_right hz2 (pow_nonneg hz 4)]
  have hE : |1 - h - D2 - D4| ≤ (25 / 6 : ℝ) * z ^ 6 :=
    leftUpper_halfEntropy_deficit_quartic_remainder hw hwz hzmax
  have hdiff : |1 - h - D2| ≤ 3 * z ^ 4 := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hE).1, (abs_le.mp hE).2, pow_nonneg hz 4]
  have hdelta : 1 - h ≤ 4 * z ^ 2 := by
    linarith [(abs_le.mp hdiff).2, sq_nonneg z]
  have hm1 : h ≤ 1 := by
    dsimp [h]
    linarith [H_le_one (1 / 2 - z), H_le_one (1 / 2 - w)]
  exact ⟨(show (9 / 10 : ℝ) ≤ h by linarith), hm1,
    (show 0 ≤ 1 - h by linarith), hdelta, hdiff⟩

private theorem contact_taylor_control {t rho delta L : ℝ}
    (ht : 0 ≤ t) (htr : t ≤ rho) (hL : (2 / 3 : ℝ) ≤ L)
    (heq : rho - t = rho * delta) (hdelta : delta ≤ t ^ 2)
    (herr : |delta - t ^ 2 / (2 * L)| ≤ t ^ 4 / 4) :
    |t - rho + rho ^ 3 / (2 * L)| ≤ (7 / 4 : ℝ) * rho ^ 5 ∧
    |t ^ 3 - rho ^ 3| ≤ 3 * rho ^ 5 := by
  have hr : 0 ≤ rho := ht.trans htr
  have hLp : 0 < L := by linarith
  have ht2 : t ^ 2 ≤ rho ^ 2 := by gcongr
  have ht4 : t ^ 4 ≤ rho ^ 4 := by gcongr
  have hgap : rho - t ≤ rho ^ 3 := by
    rw [heq]
    calc
      rho * delta ≤ rho * t ^ 2 := mul_le_mul_of_nonneg_left hdelta hr
      _ ≤ rho * rho ^ 2 := mul_le_mul_of_nonneg_left ht2 hr
      _ = rho ^ 3 := by ring
  have hsquare : rho ^ 2 - t ^ 2 ≤ 2 * rho ^ 4 := by
    have hp := mul_le_mul hgap (show rho + t ≤ 2 * rho by linarith)
      (by linarith : 0 ≤ rho + t) (pow_nonneg hr 3)
    nlinarith only [hp]
  have hsquare0 : 0 ≤ rho ^ 2 - t ^ 2 := by linarith
  have hsdiv : (rho ^ 2 - t ^ 2) / (2 * L) ≤ (3 / 2 : ℝ) * rho ^ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * L)).2
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ 3 * rho ^ 4 by positivity)]
  have htri : |(rho ^ 2 - t ^ 2) / (2 * L) + (t ^ 2 / (2 * L) - delta)| ≤
      (3 / 2 : ℝ) * rho ^ 4 + rho ^ 4 / 4 := by
    calc
      _ ≤ |(rho ^ 2 - t ^ 2) / (2 * L)| + |t ^ 2 / (2 * L) - delta| := abs_add_le _ _
      _ = (rho ^ 2 - t ^ 2) / (2 * L) + |delta - t ^ 2 / (2 * L)| := by
        rw [abs_of_nonneg (div_nonneg hsquare0 (by positivity)), abs_sub_comm]
      _ ≤ (3 / 2 : ℝ) * rho ^ 4 + rho ^ 4 / 4 := by linarith
  have hid : t - rho + rho ^ 3 / (2 * L) =
      rho * ((rho ^ 2 - t ^ 2) / (2 * L) + (t ^ 2 / (2 * L) - delta)) := by
    calc
      _ = rho ^ 3 / (2 * L) - rho * delta := by linarith only [heq]
      _ = _ := by ring
  constructor
  · rw [hid, abs_mul, abs_of_nonneg hr]
    have hp := mul_le_mul_of_nonneg_left htri hr
    nlinarith only [hp]
  · rw [abs_of_nonpos (sub_nonpos.mpr (by gcongr : t ^ 3 ≤ rho ^ 3))]
    have hmid : rho ^ 2 + rho * t + t ^ 2 ≤ 3 * rho ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left htr hr]
    have hp := mul_le_mul hgap hmid (by positivity : 0 ≤ rho ^ 2 + rho * t + t ^ 2)
      (pow_nonneg hr 3)
    nlinarith only [hp]

theorem leftUpper_F_contact_quartic_remainder {r h : ℝ}
    (hr : 0 ≤ r) (hrmax : r ≤ 1 / 64) (hhlo : (9 / 10 : ℝ) ≤ h) :
    |F r h - (2 * r ^ 2 / (Real.log 2 * h) +
      (2 / (3 * Real.log 2) - 1 / (Real.log 2) ^ 2) * r ^ 4 / h ^ 3)| ≤
      16 * r ^ 6 := by
  by_cases hr0 : r = 0
  · subst r
    norm_num [F]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hh : 0 < h := by linarith
  let v := radialContact r h
  let q := 1 / 2 - v
  let t := 2 * q
  let rho := r / h
  let L := Real.log 2
  let c := 2 / (3 * L) - 1 / L ^ 2
  have hL : (2 / 3 : ℝ) ≤ L := by dsimp [L]; linarith [Real.log_two_gt_d9]
  have hLp : 0 < L := log_two_pos
  have hv0 : 0 < v := radialContact_pos hrp hh
  have hvhalf : v < 1 / 2 := radialContact_lt_half hrp hh
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrho : 0 ≤ rho := div_nonneg hr hh.le
  have hcEq : r * H v = h * t := by
    have he := radialContact_equation hrp hh
    dsimp [v, t, q] at *
    nlinarith only [he]
  have htr : t ≤ rho := by
    apply (le_div_iff₀ hh).2
    nlinarith [mul_le_mul_of_nonneg_left (H_le_one v) hr]
  have hrhomax : rho ≤ 1 / 50 := by
    apply (div_le_iff₀ hh).2
    linarith
  have hqmax : q ≤ 1 / 64 := by dsimp [t] at htr; linarith
  have hqeq : 1 / 2 - q = v := by dsimp [q]; ring
  have hdata := leftUpper_halfEntropy_radial_data hq (le_refl q) hqmax
  have hHavg : (H (1 / 2 - q) + H (1 / 2 - q)) / 2 = H v := by rw [hqeq]; ring
  dsimp only at hdata
  rw [hHavg] at hdata
  have hdelta : 1 - H v ≤ t ^ 2 := by
    have he := hdata.2.2.2.1
    dsimp [t]
    nlinarith only [he]
  have hD2 : leftUpperHalfD2 q q L = t ^ 2 / (2 * L) := by
    dsimp [leftUpperHalfD2, t]
    ring
  have herr : |1 - H v - t ^ 2 / (2 * L)| ≤ t ^ 4 / 4 := by
    have he := hdata.2.2.2.2
    change |1 - H v - leftUpperHalfD2 q q L| ≤ 3 * q ^ 4 at he
    rw [hD2] at he
    exact he.trans (by dsimp [t]; nlinarith [pow_nonneg hq 4])
  have heq : rho - t = rho * (1 - H v) := by
    dsimp [rho]
    field_simp [ne_of_gt hh]
    nlinarith only [hcEq]
  have hTaylor := contact_taylor_control ht htr hL heq hdelta herr
  have hJ := leftUpper_J_half_bias_cubic_remainder hq hqmax
  rw [hqeq] at hJ
  have hJpoly : 4 * q / L + 16 * q ^ 3 / (3 * L) =
      (2 / L) * t + (2 / (3 * L)) * t ^ 3 := by dsimp [t]; ring
  change |J v - (4 * q / L + 16 * q ^ 3 / (3 * L))| ≤ 25 * q ^ 5 at hJ
  rw [hJpoly] at hJ
  have hq5 : q ^ 5 ≤ (rho / 2) ^ 5 := by
    have hqr : q ≤ rho / 2 := by dsimp [t] at htr; linarith
    gcongr
  have hJerr : |J v - ((2 / L) * t + (2 / (3 * L)) * t ^ 3)| ≤
      (25 / 32 : ℝ) * rho ^ 5 := by nlinarith only [hJ, hq5]
  have hA0 : 0 ≤ 2 / L := by positivity
  have hA : 2 / L ≤ 3 := (div_le_iff₀ hLp).2 (by linarith)
  have hB0 : 0 ≤ 2 / (3 * L) := by positivity
  have hB : 2 / (3 * L) ≤ 1 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hT1 : |(2 / L) * (t - rho + rho ^ 3 / (2 * L))| ≤
      (21 / 4 : ℝ) * rho ^ 5 := by
    rw [abs_mul, abs_of_nonneg hA0]
    have hp := mul_le_mul hA hTaylor.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith only [hp]
  have hT3 : |(2 / (3 * L)) * (t ^ 3 - rho ^ 3)| ≤ 3 * rho ^ 5 := by
    rw [abs_mul, abs_of_nonneg hB0]
    simpa only [one_mul] using
      mul_le_mul hB hTaylor.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hJid : J v - ((2 / L) * rho + c * rho ^ 3) =
      (J v - ((2 / L) * t + (2 / (3 * L)) * t ^ 3)) +
      (2 / L) * (t - rho + rho ^ 3 / (2 * L)) +
      (2 / (3 * L)) * (t ^ 3 - rho ^ 3) := by
    dsimp [c]
    field_simp [ne_of_gt hLp] <;> ring
  have hJtotal : |J v - ((2 / L) * rho + c * rho ^ 3)| ≤
      (289 / 32 : ℝ) * rho ^ 5 := by
    rw [hJid]
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hJerr).1, (abs_le.mp hJerr).2,
      (abs_le.mp hT1).1, (abs_le.mp hT1).2, (abs_le.mp hT3).1, (abs_le.mp hT3).2]
  have hFid : F r h - (2 * r ^ 2 / (L * h) + c * r ^ 4 / h ^ 3) =
      r * (J v - ((2 / L) * rho + c * rho ^ 3)) := by
    rw [F, if_neg hr0]
    dsimp [v, rho]
    field_simp [ne_of_gt hh, ne_of_gt hLp] <;> ring
  change |F r h - (2 * r ^ 2 / (L * h) + c * r ^ 4 / h ^ 3)| ≤ _
  rw [hFid, abs_mul, abs_of_nonneg hr]
  calc
    _ ≤ r * ((289 / 32 : ℝ) * rho ^ 5) := mul_le_mul_of_nonneg_left hJtotal hr
    _ = ((289 / 32 : ℝ) * r ^ 6) / h ^ 5 := by dsimp [rho]; ring
    _ ≤ 16 * r ^ 6 := by
      apply (div_le_iff₀ (pow_pos hh 5)).2
      have hh5 : (9 / 10 : ℝ) ^ 5 ≤ h ^ 5 := by gcongr
      have hc : (289 / 32 : ℝ) ≤ 16 * h ^ 5 := by nlinarith only [hh5]
      nlinarith only [mul_le_mul_of_nonneg_right hc (pow_nonneg hr 6)]

#print axioms leftUpper_halfEntropy_radial_data
#print axioms leftUpper_F_contact_quartic_remainder

end GeneralCK

end


