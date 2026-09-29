-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerEntropyBounds
-- name    : CK_GeneralCK_CorrectionHighUNearCornerEntropyBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T05:46:53.62698+00:00
-- url     : https://prove2.me/theorems/58766595-d0ee-4e66-8f15-a9c034bda8e8
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHighUNearCornerEntropyBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHighUNearCornerEntropyBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHighUNearCornerEntropyBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHighUNearCornerEntropyBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHighUNearCornerEntropyBounds.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerRegularContact

/-! Quantitative entropy estimates needed for the second-order left minor. -/

namespace GeneralCK.Correction.HighU

open Certificates.Mixed

theorem nearCorner_log_two_lower : (69 / 100 : ℝ) ≤ Real.log 2 := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 2
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem nearCorner_entropy_loss
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 100) :
    2 * t ^ 2 ≤ Real.log 2 - hn (1 / 2 - t) ∧
      Real.log 2 - hn (1 / 2 - t) ≤ (2001 / 1000 : ℝ) * t ^ 2 := by
  let r : ℝ := 2 * t
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hr2 : r ^ 2 ≤ (1 / 2500 : ℝ) := by dsimp [r]; nlinarith
  have hden : 0 < 1 - r ^ 2 := by linarith
  have ha : SmallMean.A r ≤ (2001 / 2000 : ℝ) * r := by
    apply (SmallMean.A_upper hr0 hr1).trans
    apply (div_le_iff₀ hden).2
    have hp := mul_nonneg hr0 (sub_nonneg.mpr hr2)
    nlinarith only [hp, hr0]
  have hcl := SmallMean.Cn_ge_half_sq hr0 hr1.le
  have hcu := SmallMean.Cn_dilation_derivative_nonneg hr0 hr1
  have hp := mul_le_mul_of_nonneg_left ha hr0
  have heq : SmallMean.Cn r = Real.log 2 - hn (1 / 2 - t) := by
    rw [Certificates.Mixed.hn_eq_H_mul_log]
    unfold SmallMean.Cn
    rw [show (1 - r) / 2 = 1 / 2 - t by dsimp [r]; ring]
    ring
  rw [heq] at hcl hcu
  dsimp [r] at hcl hcu hp
  constructor <;> nlinarith only [hcl, hcu, hp]

theorem nearCorner_entropySum_enclosure
    {t rho : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 100)
    (hr : 0 ≤ rho) (hr1 : rho ≤ 1 / 100) :
    2 * Real.log 2 - (2001 / 500 : ℝ) * t ^ 2 ≤
        Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - rho) * t) ∧
      Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - rho) * t) ≤ 2 * Real.log 2 := by
  have hkt0 : 0 ≤ (1 - rho) * t := mul_nonneg (by linarith) ht
  have hktt : (1 - rho) * t ≤ t := by nlinarith only [mul_nonneg hr ht]
  have hktu : (1 - rho) * t ≤ 1 / 100 := hktt.trans ht1
  have hktsq : ((1 - rho) * t) ^ 2 ≤ t ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hktt) (add_nonneg ht hkt0)]
  have hu := nearCorner_entropy_loss ht ht1
  have hw := nearCorner_entropy_loss hkt0 hktu
  unfold Natural.entropySum
  constructor <;> nlinarith only [hu.1, hu.2, hw.1, hw.2, hktsq, sq_nonneg t,
    sq_nonneg ((1 - rho) * t)]

#print axioms nearCorner_log_two_lower
#print axioms nearCorner_entropy_loss
#print axioms nearCorner_entropySum_enclosure

end GeneralCK.Correction.HighU


