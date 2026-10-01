-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarMiddleEta
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarMiddleEta
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:27:14.152773+00:00
-- url     : https://prove2.me/theorems/94ae00e2-f97a-4a4b-979f-61515bc4f3de
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarMiddleEta` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarMiddleEta` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarMiddleEta` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperHalfCollarMiddleEta (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperHalfCollarMiddleEta.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarEntropyJet

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperHalfCollarMiddleEta =====
section

/-! Middle-entropy eta remainder for the actual lower entropy inverse. -/

namespace GeneralCK

private theorem quartic_square_control {z delta D2 D4 : ℝ}
    (hz : 0 ≤ z) (hzmax : z ≤ 1 / 64) (hdelta : 0 ≤ delta)
    (hD20 : 0 ≤ D2) (hD2 : D2 ≤ 3 * z ^ 2)
    (hD40 : 0 ≤ D4) (hD4 : D4 ≤ 2 * z ^ 4)
    (herr : |delta - D2 - D4| ≤ (25 / 6 : ℝ) * z ^ 6) :
    delta ≤ 4 * z ^ 2 ∧ |delta ^ 2 - D2 ^ 2| ≤ 16 * z ^ 6 := by
  have hz2 : z ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := by gcongr
  have hz4 : z ^ 4 ≤ z ^ 2 / 4096 := by
    nlinarith only [mul_le_mul_of_nonneg_right hz2 (sq_nonneg z)]
  have hz6 : z ^ 6 ≤ z ^ 4 / 4096 := by
    nlinarith only [mul_le_mul_of_nonneg_right hz2 (pow_nonneg hz 4)]
  have hdiff : |delta - D2| ≤ (9 / 4 : ℝ) * z ^ 4 := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp herr).1, (abs_le.mp herr).2,
      pow_nonneg hz 4]
  have hdup : delta ≤ 4 * z ^ 2 := by
    linarith [(abs_le.mp hdiff).2, sq_nonneg z]
  refine ⟨hdup, ?_⟩
  have hsum : |delta + D2| ≤ 7 * z ^ 2 := by
    rw [abs_of_nonneg (add_nonneg hdelta hD20)]
    linarith
  calc
    |delta ^ 2 - D2 ^ 2| = |delta - D2| * |delta + D2| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ ((9 / 4 : ℝ) * z ^ 4) * (7 * z ^ 2) :=
      mul_le_mul hdiff hsum (abs_nonneg _) (by positivity)
    _ ≤ 16 * z ^ 6 := by nlinarith [pow_nonneg hz 6]

private theorem half_jet_bounds {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) :
    0 ≤ leftUpperHalfD2 z w (Real.log 2) ∧
    leftUpperHalfD2 z w (Real.log 2) ≤ 3 * z ^ 2 ∧
    0 ≤ leftUpperHalfD4 z w (Real.log 2) ∧
    leftUpperHalfD4 z w (Real.log 2) ≤ 2 * z ^ 4 := by
  have hz := hw.trans hwz
  have hL : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hw2 : w ^ 2 ≤ z ^ 2 := by gcongr
  have hw4 : w ^ 4 ≤ z ^ 4 := by gcongr
  refine ⟨by unfold leftUpperHalfD2; positivity, ?_,
    by unfold leftUpperHalfD4; positivity, ?_⟩
  · unfold leftUpperHalfD2
    apply (div_le_iff₀ log_two_pos).2
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ 3 * z ^ 2 by positivity)]
  · unfold leftUpperHalfD4
    apply (div_le_iff₀ (by positivity : 0 < 3 * Real.log 2)).2
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ 6 * z ^ 4 by positivity)]

theorem leftUpper_halfEntropy_deficit_quartic_remainder {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 64) :
    |(1 - (H (1 / 2 - z) + H (1 / 2 - w)) / 2) -
        leftUpperHalfD2 z w (Real.log 2) -
        leftUpperHalfD4 z w (Real.log 2)| ≤ (25 / 6 : ℝ) * z ^ 6 := by
  have hz := hw.trans hwz
  have hEz := leftUpper_entropy_half_bias_quartic_remainder hz hzmax
  have hEw := leftUpper_entropy_half_bias_quartic_remainder hw (hwz.trans hzmax)
  have hw6 : w ^ 6 ≤ z ^ 6 := by gcongr
  have heq : (1 - (H (1 / 2 - z) + H (1 / 2 - w)) / 2) -
      leftUpperHalfD2 z w (Real.log 2) - leftUpperHalfD4 z w (Real.log 2) =
      ((1 - H (1 / 2 - z) - (2 * z ^ 2 / Real.log 2 + 4 * z ^ 4 / (3 * Real.log 2))) +
       (1 - H (1 / 2 - w) - (2 * w ^ 2 / Real.log 2 + 4 * w ^ 4 / (3 * Real.log 2)))) / 2 := by
    unfold leftUpperHalfD2 leftUpperHalfD4
    ring
  rw [heq]
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hEz).1, (abs_le.mp hEz).2,
    (abs_le.mp hEw).1, (abs_le.mp hEw).2]

theorem leftUpper_eta_deficit_quadratic_remainder {q : ℝ}
    (hq : 0 ≤ q) (hqmax : q ≤ 1 / 64) :
    |eta (H (1 / 2 - q)) -
      (4 * (1 - H (1 / 2 - q)) +
        (4 * Real.log 2 / 3) * (1 - H (1 / 2 - q)) ^ 2)| ≤ 83 * q ^ 6 := by
  let delta := 1 - H (1 / 2 - q)
  let D2 := leftUpperHalfD2 q q (Real.log 2)
  let D4 := leftUpperHalfD4 q q (Real.log 2)
  have hD := half_jet_bounds hq (le_refl q)
  have hE : |delta - D2 - D4| ≤ (25 / 6 : ℝ) * q ^ 6 := by
    convert leftUpper_halfEntropy_deficit_quartic_remainder hq (le_refl q) hqmax using 1 <;>
      dsimp [delta, D2, D4] <;> ring
  have hdelta : 0 ≤ delta := sub_nonneg.mpr (H_le_one _)
  have hsq := (quartic_square_control hq hqmax hdelta hD.1 hD.2.1
    hD.2.2.1 hD.2.2.2 hE).2
  have hc0 : 0 ≤ 4 * Real.log 2 / 3 := by positivity
  have hc1 : 4 * Real.log 2 / 3 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hprod : |(4 * Real.log 2 / 3) * (delta ^ 2 - D2 ^ 2)| ≤ 16 * q ^ 6 := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc
      _ ≤ 1 * (16 * q ^ 6) := mul_le_mul hc1 hsq (abs_nonneg _) (by norm_num)
      _ = 16 * q ^ 6 := one_mul _
  have hEta := leftUpper_eta_half_bias_quartic_remainder hq hqmax
  have hjet : 2 * leftUpperHalfEtaBJet q (Real.log 2) =
      4 * D2 + 4 * D4 + (4 * Real.log 2 / 3) * D2 ^ 2 := by
    dsimp [D2, D4, leftUpperHalfEtaBJet, leftUpperHalfD2, leftUpperHalfD4]
    field_simp [ne_of_gt log_two_pos]
    ring
  have heq : eta (H (1 / 2 - q)) - (4 * delta + (4 * Real.log 2 / 3) * delta ^ 2) =
      2 * (eta (H (1 / 2 - q)) / 2 - leftUpperHalfEtaBJet q (Real.log 2)) -
      4 * (delta - D2 - D4) - (4 * Real.log 2 / 3) * (delta ^ 2 - D2 ^ 2) := by
    linarith only [hjet]
  change |eta (H (1 / 2 - q)) - (4 * delta + (4 * Real.log 2 / 3) * delta ^ 2)| ≤ _
  rw [heq]
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hEta).1, (abs_le.mp hEta).2,
    (abs_le.mp hE).1, (abs_le.mp hE).2, (abs_le.mp hprod).1,
    (abs_le.mp hprod).2, pow_nonneg hq 6]

theorem leftUpper_middle_eta_quartic_remainder {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 64) :
    |eta ((H (1 / 2 - z) + H (1 / 2 - w)) / 2) -
      leftUpperHalfEtaJet (leftUpperHalfD2 z w (Real.log 2))
        (leftUpperHalfD4 z w (Real.log 2)) (Real.log 2)| ≤ 116 * z ^ 6 := by
  have hz := hw.trans hwz
  let h := (H (1 / 2 - z) + H (1 / 2 - w)) / 2
  let delta := 1 - h
  let D2 := leftUpperHalfD2 z w (Real.log 2)
  let D4 := leftUpperHalfD4 z w (Real.log 2)
  have hm0 : 0 ≤ h := by
    have ha := H_pos (show 0 < 1 / 2 - z by linarith)
      (show 1 / 2 - z < 1 by linarith)
    have hb := H_pos (show 0 < 1 / 2 - w by linarith)
      (show 1 / 2 - w < 1 by linarith)
    dsimp [h]
    linarith
  have hm1 : h ≤ 1 := by
    dsimp [h]
    linarith [H_le_one (1 / 2 - z), H_le_one (1 / 2 - w)]
  have hinv := leftUpper_halfEntropyInverse_between
    (show 0 ≤ 1 / 2 - z by linarith)
    (show 1 / 2 - z ≤ 1 / 2 - w by linarith)
    (show 1 / 2 - w ≤ 1 / 2 by linarith)
  let q := 1 / 2 - entropyInverse h
  have hq0 : 0 ≤ q := by
    change 0 ≤ 1 / 2 - entropyInverse h
    change _ ∧ entropyInverse h ≤ 1 / 2 - w at hinv
    linarith [hinv.2]
  have hqz : q ≤ z := by
    change 1 / 2 - entropyInverse h ≤ z
    change 1 / 2 - z ≤ entropyInverse h ∧ _ at hinv
    linarith [hinv.1]
  have hEq : H (1 / 2 - q) = h := by
    simpa only [q, sub_sub_cancel] using (entropyInverse_spec hm0 hm1).2.2
  have hEtaq := leftUpper_eta_deficit_quadratic_remainder hq0 (hqz.trans hzmax)
  rw [hEq] at hEtaq
  have hEta : |eta h - (4 * delta + (4 * Real.log 2 / 3) * delta ^ 2)| ≤
      83 * z ^ 6 := hEtaq.trans (by gcongr)
  have hD := half_jet_bounds hw hwz
  have hE : |delta - D2 - D4| ≤ (25 / 6 : ℝ) * z ^ 6 :=
    leftUpper_halfEntropy_deficit_quartic_remainder hw hwz hzmax
  have hsq := (quartic_square_control hz hzmax (show 0 ≤ delta from sub_nonneg.mpr hm1)
    hD.1 hD.2.1 hD.2.2.1 hD.2.2.2 hE).2
  have hc0 : 0 ≤ 4 * Real.log 2 / 3 := by positivity
  have hc1 : 4 * Real.log 2 / 3 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hprod : |(4 * Real.log 2 / 3) * (delta ^ 2 - D2 ^ 2)| ≤ 16 * z ^ 6 := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc
      _ ≤ 1 * (16 * z ^ 6) := mul_le_mul hc1 hsq (abs_nonneg _) (by norm_num)
      _ = 16 * z ^ 6 := one_mul _
  have heq : eta h - leftUpperHalfEtaJet D2 D4 (Real.log 2) =
      (eta h - (4 * delta + (4 * Real.log 2 / 3) * delta ^ 2)) +
      4 * (delta - D2 - D4) + (4 * Real.log 2 / 3) * (delta ^ 2 - D2 ^ 2) := by
    unfold leftUpperHalfEtaJet
    ring
  change |eta h - leftUpperHalfEtaJet D2 D4 (Real.log 2)| ≤ _
  rw [heq]
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hEta).1, (abs_le.mp hEta).2,
    (abs_le.mp hE).1, (abs_le.mp hE).2, (abs_le.mp hprod).1,
    (abs_le.mp hprod).2, pow_nonneg hz 6]

#print axioms leftUpper_halfEntropy_deficit_quartic_remainder
#print axioms leftUpper_eta_deficit_quadratic_remainder
#print axioms leftUpper_middle_eta_quartic_remainder

end GeneralCK

end


