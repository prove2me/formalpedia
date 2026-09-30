-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryEntropyBounds
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryEntropyBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:02:06.846139+00:00
-- url     : https://prove2.me/theorems/918eddf5-25e0-46be-a810-48cbccb10649
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryEntropyBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryEntropyBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryEntropyBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryEntropyBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryEntropyBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ZeroCapLeftStationaryLogEnclosures
import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanBounds
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryEntropyBounds =====
section

/-! Exact rational entropy bounds for the narrow zero-cap stationary chart.
Source-only until direct Lean compilation and named audit. -/

namespace GeneralCK
open Certificates.ZeroCapLeftStationaryLogEnclosures
namespace ZeroCapLeftStationaryEntropyBounds

theorem H_eighth_lower : (323 / 600 : ℝ) ≤ H (1 / 8) := by
  have hp : (7 : ℝ) ^ (75 : ℕ) ≤ (2 : ℝ) ^ (211 : ℕ) := by norm_num
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (7 : ℝ) ^ (75 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  have he := Certificates.SmallMean.entropy_log_identity (1 / 8 : ℝ)
  have h8 : -Real.log (1 / 8 : ℝ) = 3 * Real.log 2 := by
    rw [show (1 / 8 : ℝ) = ((2 : ℝ) ^ (3 : ℕ))⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    ring
  have h7 : -Real.log (1 - (1 / 8 : ℝ)) =
      3 * Real.log 2 - Real.log 7 := by
    rw [show 1 - (1 / 8 : ℝ) = (7 : ℝ) / 8 by norm_num,
      Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)]
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    ring
  rw [h8, h7] at he
  have hm : (323 / 600 : ℝ) * Real.log 2 ≤ H (1 / 8) * Real.log 2 := by
    nlinarith only [he, hl]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hm)

theorem H_Bmax_upper : H (65 / 512) ≤ (57 / 100 : ℝ) := by
  have he := Certificates.SmallMean.entropy_log_identity (65 / 512 : ℝ)
  have hA := entropy_Bmax_A.2
  have hB := entropy_Bmax_B.2
  have htwo := Certificates.PilotData.log_two.1
  norm_num only [div_one] at htwo
  have hnum : (65 / 512 : ℝ) * (-Real.log (65 / 512)) +
      (1 - 65 / 512) * (-Real.log (1 - (65 / 512 : ℝ))) ≤
      (65 / 512) * (2063937357 / 1000000000) +
        (1 - 65 / 512) * (135766031 / 1000000000) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
      (mul_le_mul_of_nonneg_left hB (by norm_num))
  have hscale : (57 / 100 : ℝ) * (34657359 / 50000000) ≤
      (57 / 100) * Real.log 2 :=
    mul_le_mul_of_nonneg_left htwo (by norm_num)
  nlinarith only [he, hnum, hscale]

theorem narrow_box_entropy_bounds {a b : ℝ}
    (ha : 1 / 8 ≤ a) (ha' : a ≤ 129 / 1024)
    (hb : 129 / 1024 ≤ b) (hb' : b ≤ 65 / 512) :
    323 / 300 ≤ H a + H b ∧ H a + H b ≤ 57 / 50 ∧ H b ≤ 57 / 100 := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hab : a ≤ b := ha'.trans hb
  have hHaLower : H (1 / 8) ≤ H a := H_strictMonoOn.monotoneOn
    ⟨by norm_num, by norm_num⟩ ⟨ha0, by linarith⟩ ha
  have hHaB : H a ≤ H b := H_strictMonoOn.monotoneOn
    ⟨ha0, by linarith⟩ ⟨hb0, by linarith⟩ hab
  have hBupper : H b ≤ H (65 / 512) := H_strictMonoOn.monotoneOn
    ⟨hb0, by linarith⟩ ⟨by norm_num, by norm_num⟩ hb'
  constructor
  · linarith [H_eighth_lower]
  constructor
  · linarith [H_Bmax_upper]
  · linarith [H_Bmax_upper]

end ZeroCapLeftStationaryEntropyBounds

#print axioms GeneralCK.ZeroCapLeftStationaryEntropyBounds.H_eighth_lower
#print axioms GeneralCK.ZeroCapLeftStationaryEntropyBounds.H_Bmax_upper
#print axioms GeneralCK.ZeroCapLeftStationaryEntropyBounds.narrow_box_entropy_bounds

end GeneralCK

end


