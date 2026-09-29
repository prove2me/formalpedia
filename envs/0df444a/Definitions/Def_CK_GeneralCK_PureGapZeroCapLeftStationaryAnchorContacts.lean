-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryAnchorContacts
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryAnchorContacts
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:00:55.971442+00:00
-- url     : https://prove2.me/theorems/15cbd154-eccc-4a5a-862d-54e2d6fc483b
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryAnchorContacts` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryAnchorContacts` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryAnchorContacts` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryAnchorContacts (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryAnchorContacts.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryThetaBracketBridge
import Definitions.Def_CK_GeneralCK_Certificates_ZeroCapLeftStationaryLogEnclosures
import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanBounds

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryAnchorContacts =====
section

/-! Source-only exact-contact brackets for three zero-cap stationary anchors.
The log enclosures themselves are kernel-checkable 20-term witnesses. -/

namespace GeneralCK
open Certificates.ZeroCapLeftStationaryLogEnclosures
open ZeroCapLeftStationaryThetaBracket
namespace ZeroCapLeftStationaryAnchorContacts

private theorem H_lower_from_log_box {v e Al Bl : ℝ}
    (hv : 0 ≤ v) (hv' : v ≤ 1) (he : 0 ≤ e)
    (hA : Al ≤ -Real.log v) (hB : Bl ≤ -Real.log (1 - v))
    (hnumeric : e * (693147181 / 1000000000) ≤ v * Al + (1 - v) * Bl) :
    e ≤ H v := by
  have htwo := Certificates.PilotData.log_two.2
  norm_num only [div_one] at htwo
  have hsum : v * Al + (1 - v) * Bl ≤
      v * (-Real.log v) + (1 - v) * (-Real.log (1 - v)) :=
    add_le_add (mul_le_mul_of_nonneg_left hA hv)
      (mul_le_mul_of_nonneg_left hB (by linarith))
  have heq := Certificates.SmallMean.entropy_log_identity v
  have hscale := mul_le_mul_of_nonneg_left htwo he
  have hmul : e * Real.log 2 ≤ H v * Real.log 2 := by
    linarith only [hnumeric, hsum, heq, hscale]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hmul)

private theorem H_upper_from_log_box {v e Au Bu : ℝ}
    (hv : 0 ≤ v) (hv' : v ≤ 1) (he : 0 ≤ e)
    (hA : -Real.log v ≤ Au) (hB : -Real.log (1 - v) ≤ Bu)
    (hnumeric : v * Au + (1 - v) * Bu ≤ e * (34657359 / 50000000)) :
    H v ≤ e := by
  have htwo := Certificates.PilotData.log_two.1
  norm_num only [div_one] at htwo
  have hsum : v * (-Real.log v) + (1 - v) * (-Real.log (1 - v)) ≤
      v * Au + (1 - v) * Bu :=
    add_le_add (mul_le_mul_of_nonneg_left hA hv)
      (mul_le_mul_of_nonneg_left hB (by linarith))
  have heq := Certificates.SmallMean.entropy_log_identity v
  have hscale := mul_le_mul_of_nonneg_left htwo he
  have hmul : H v * Real.log 2 ≤ e * Real.log 2 := by
    linarith only [hnumeric, hsum, heq, hscale]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hmul)

theorem contact1_upper :
    radialContact (2 * (3175 / 29184 : ℝ)) 1 ≤ 3949 / 10000 := by
  have hH : (967 / 1000 : ℝ) ≤ H (3949 / 10000) :=
    H_lower_from_log_box (by norm_num) (by norm_num) (by norm_num)
      theta1_A.1 theta1_B.1 (by norm_num)
  exact contact_upper_of_entropy_lower (by norm_num) (by norm_num)
    (by norm_num) hH (by norm_num)

theorem contact2_upper :
    radialContact (2 * (25 / 76 : ℝ)) 1 ≤ 299 / 1250 := by
  have hH : (793 / 1000 : ℝ) ≤ H (299 / 1250) :=
    H_lower_from_log_box (by norm_num) (by norm_num) (by norm_num)
      theta2_A.1 theta2_B.1 (by norm_num)
  exact contact_upper_of_entropy_lower (by norm_num) (by norm_num)
    (by norm_num) hH (by norm_num)

theorem contact3_lower :
    (37 / 250 : ℝ) ≤ radialContact (2 * (375 / 646 : ℝ)) 1 := by
  have hH : H (37 / 250) ≤ (606 / 1000 : ℝ) :=
    H_upper_from_log_box (by norm_num) (by norm_num) (by norm_num)
      theta3_A.2 theta3_B.2 (by norm_num)
  exact contact_lower_of_entropy_upper (by norm_num) (by norm_num)
    (by norm_num) hH (by norm_num)

end ZeroCapLeftStationaryAnchorContacts

#print axioms GeneralCK.ZeroCapLeftStationaryAnchorContacts.contact1_upper
#print axioms GeneralCK.ZeroCapLeftStationaryAnchorContacts.contact2_upper
#print axioms GeneralCK.ZeroCapLeftStationaryAnchorContacts.contact3_lower

end GeneralCK

end


