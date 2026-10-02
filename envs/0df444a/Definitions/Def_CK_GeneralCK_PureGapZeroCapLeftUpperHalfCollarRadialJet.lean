-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarRadialJet
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarRadialJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T14:35:23.949292+00:00
-- url     : https://prove2.me/theorems/c5a55046-98bb-430b-b6eb-2498a7d32cfd
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarRadialJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarRadialJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarRadialJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperHalfCollarRadialJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperHalfCollarRadialJet.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarRadialContactJet

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperHalfCollarRadialJet =====
section

namespace GeneralCK

theorem leftUpper_F_half_bias_quartic_remainder {z w r : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 64)
    (hr : 0 ≤ r) (hrz : r ≤ z) :
    |F r ((H (1 / 2 - z) + H (1 / 2 - w)) / 2) -
      leftUpperHalfFJet r (leftUpperHalfD2 z w (Real.log 2)) (Real.log 2)| ≤
      120 * z ^ 6 := by
  have hz := hw.trans hwz
  let h := (H (1 / 2 - z) + H (1 / 2 - w)) / 2
  let delta := 1 - h
  let D2 := leftUpperHalfD2 z w (Real.log 2)
  let L := Real.log 2
  let c := 2 / (3 * L) - 1 / L ^ 2
  have hdata := leftUpper_halfEntropy_radial_data hw hwz hzmax
  change (9 / 10 : ℝ) ≤ h ∧ h ≤ 1 ∧ 0 ≤ delta ∧ delta ≤ 4 * z ^ 2 ∧
    |delta - D2| ≤ 3 * z ^ 4 at hdata
  have hh : 0 < h := by linarith [hdata.1]
  have hdelta0 : 0 ≤ delta := hdata.2.2.1
  have hdeltaBound : delta ≤ 4 * z ^ 2 := hdata.2.2.2.1
  have hLp : 0 < L := log_two_pos
  have hL : (2 / 3 : ℝ) ≤ L := by dsimp [L]; linarith [Real.log_two_gt_d9]
  have hLhi : L ≤ 3 / 4 := by dsimp [L]; linarith [Real.log_two_lt_d9]
  have hdelta2 : delta ^ 2 ≤ 16 * z ^ 4 := by
    calc
      delta ^ 2 ≤ (4 * z ^ 2) ^ 2 := by gcongr
      _ = 16 * z ^ 4 := by ring
  have hdeltaDiv : delta ^ 2 / h ≤ 18 * z ^ 4 := by
    apply (div_le_iff₀ hh).2
    nlinarith [mul_le_mul_of_nonneg_right hdata.1 (show 0 ≤ 18 * z ^ 4 by positivity)]
  have hinvId : 1 / h - 1 - D2 = (delta - D2) + delta ^ 2 / h := by
    dsimp [delta]
    field_simp [ne_of_gt hh] <;> ring
  have hinv : |1 / h - 1 - D2| ≤ 21 * z ^ 4 := by
    rw [hinvId]
    have ha := abs_add_le (delta - D2) (delta ^ 2 / h)
    rw [abs_of_nonneg (div_nonneg (sq_nonneg delta) hh.le)] at ha
    linarith [hdata.2.2.2.2]
  have hh2 : h ^ 2 ≤ 1 := by
    have hp := mul_le_mul hdata.2.1 hdata.2.1 hh.le (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [hp]
  have hnum : delta * (1 + h + h ^ 2) ≤ 12 * z ^ 2 := by
    have hp := mul_le_mul hdata.2.2.2.1 (show 1 + h + h ^ 2 ≤ 3 by linarith [hdata.2.1])
      (by positivity : 0 ≤ 1 + h + h ^ 2) (by positivity : 0 ≤ 4 * z ^ 2)
    nlinarith only [hp]
  have hinv3Id : 1 / h ^ 3 - 1 = delta * (1 + h + h ^ 2) / h ^ 3 := by
    dsimp [delta]
    field_simp [ne_of_gt hh] <;> ring
  have hinv3 : |1 / h ^ 3 - 1| ≤ 17 * z ^ 2 := by
    rw [hinv3Id, abs_of_nonneg (by positivity :
      0 ≤ delta * (1 + h + h ^ 2) / h ^ 3)]
    apply (div_le_iff₀ (pow_pos hh 3)).2
    have hh3 : (9 / 10 : ℝ) ^ 3 ≤ h ^ 3 := by gcongr; exact hdata.1
    have hc : (12 : ℝ) ≤ 17 * h ^ 3 := by nlinarith only [hh3]
    nlinarith only [hnum, mul_le_mul_of_nonneg_right hc (sq_nonneg z)]
  have hcForm : c = (2 * L - 3) / (3 * L ^ 2) := by
    dsimp [c]
    field_simp [ne_of_gt hLp] <;> ring
  have hcabs : |c| ≤ 2 := by
    rw [hcForm]
    have hden : 0 < 3 * L ^ 2 := by positivity
    apply abs_le.mpr
    constructor
    · apply (le_div_iff₀ hden).2
      nlinarith [sq_nonneg (L - 2 / 3)]
    · exact (div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le).trans (by norm_num)
  have hA0 : 0 ≤ 2 / L := by positivity
  have hA : 2 / L ≤ 3 := (div_le_iff₀ hLp).2 (by linarith)
  have hr2 : r ^ 2 ≤ z ^ 2 := by gcongr
  have hr4 : r ^ 4 ≤ z ^ 4 := by gcongr
  have hr6 : r ^ 6 ≤ z ^ 6 := by gcongr
  have hContact : |F r h - (2 * r ^ 2 / (L * h) + c * r ^ 4 / h ^ 3)| ≤
      16 * z ^ 6 :=
    (leftUpper_F_contact_quartic_remainder hr (hrz.trans hzmax) hdata.1).trans
      (mul_le_mul_of_nonneg_left hr6 (by norm_num))
  have hLeading : |((2 / L) * r ^ 2) * (1 / h - 1 - D2)| ≤ 63 * z ^ 6 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 / L) * r ^ 2)]
    have hAr : (2 / L) * r ^ 2 ≤ 3 * z ^ 2 :=
      mul_le_mul hA hr2 (sq_nonneg r) (by norm_num)
    have hp := mul_le_mul hAr hinv (abs_nonneg _) (by positivity : 0 ≤ 3 * z ^ 2)
    nlinarith only [hp]
  have hFourth : |(c * r ^ 4) * (1 / h ^ 3 - 1)| ≤ 34 * z ^ 6 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr 4)]
    have hCr : |c| * r ^ 4 ≤ 2 * z ^ 4 :=
      mul_le_mul hcabs hr4 (pow_nonneg hr 4) (by norm_num)
    have hp := mul_le_mul hCr hinv3 (abs_nonneg _) (by positivity : 0 ≤ 2 * z ^ 4)
    nlinarith only [hp]
  have heq : F r h - leftUpperHalfFJet r D2 L =
      (F r h - (2 * r ^ 2 / (L * h) + c * r ^ 4 / h ^ 3)) +
      ((2 / L) * r ^ 2) * (1 / h - 1 - D2) +
      (c * r ^ 4) * (1 / h ^ 3 - 1) := by
    dsimp [leftUpperHalfFJet, c]
    ring
  change |F r h - leftUpperHalfFJet r D2 L| ≤ _
  rw [heq]
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hContact).1, (abs_le.mp hContact).2,
    (abs_le.mp hLeading).1, (abs_le.mp hLeading).2,
    (abs_le.mp hFourth).1, (abs_le.mp hFourth).2, pow_nonneg hz 6]

#print axioms leftUpper_F_half_bias_quartic_remainder

end GeneralCK

end


