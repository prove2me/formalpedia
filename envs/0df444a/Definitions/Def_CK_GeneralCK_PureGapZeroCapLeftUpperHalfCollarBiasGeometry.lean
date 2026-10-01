-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarBiasGeometry
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarBiasGeometry
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:11:33.205135+00:00
-- url     : https://prove2.me/theorems/a6e3e7f4-514f-49ea-bca6-0f5ae2556433
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarBiasGeometry` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarBiasGeometry` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarBiasGeometry` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperHalfCollarBiasGeometry (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperHalfCollarBiasGeometry.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarQuartic

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperHalfCollarBiasGeometry =====
section

/-!
Actual-law bias containment used in the proposed left-upper real-series
half-collar remainder. The entropy inverse and radial contact remain the
project's sInf definitions; no power-series premise is used here.
-/

namespace GeneralCK

theorem leftUpper_halfEntropyInverse_between {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    a ≤ entropyInverse ((H a + H b) / 2) ∧
      entropyInverse ((H a + H b) / 2) ≤ b := by
  have haHalf : a ≤ 1 / 2 := hab.trans hb
  have hb0 : 0 ≤ b := ha.trans hab
  have hHa : 0 ≤ H a := H_nonneg ha (by linarith)
  have hHb : 0 ≤ H b := H_nonneg hb0 (by linarith)
  have horder : H a ≤ H b :=
    H_strictMonoOn.monotoneOn ⟨ha, haHalf⟩ ⟨hb0, hb⟩ hab
  have hmid0 : 0 ≤ (H a + H b) / 2 := by linarith
  have hmid1 : (H a + H b) / 2 ≤ 1 := by
    have h1 := H_le_one b
    linarith
  constructor
  · simpa only [entropyInverse_H_lower ha haHalf] using
      (entropyInverse_mono hHa hmid1 (by linarith : H a ≤ (H a + H b) / 2))
  · simpa only [entropyInverse_H_lower hb0 hb] using
      (entropyInverse_mono hmid0 (H_le_one b)
        (by linarith : (H a + H b) / 2 ≤ H b))

theorem leftUpper_radialContact_bias_upper {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) :
    1 / 2 - radialContact r h ≤ r / (2 * h) := by
  let v := radialContact r h
  have heq : r * H v = h * (1 - 2 * v) := radialContact_equation hr hh
  have hH : H v ≤ 1 := H_le_one v
  have hbound : h * (1 - 2 * v) ≤ r := by
    rw [← heq]
    nlinarith [hH]
  apply (le_div_iff₀ (by positivity : 0 < 2 * h)).2
  dsimp [v] at *
  nlinarith

#print axioms leftUpper_halfEntropyInverse_between
#print axioms leftUpper_radialContact_bias_upper

end GeneralCK

end


