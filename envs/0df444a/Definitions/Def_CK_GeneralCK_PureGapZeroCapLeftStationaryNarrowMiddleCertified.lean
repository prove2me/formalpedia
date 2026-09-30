-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryNarrowMiddleCertified
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryNarrowMiddleCertified
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:09:20.507687+00:00
-- url     : https://prove2.me/theorems/04a0d783-f7a5-46ab-9355-2d78e803a753
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddleCertified` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddleCertified` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddleCertified` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddleCertified (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryNarrowMiddleCertified.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryEntropyBounds
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryRadialSlopeIntervals
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryNarrowMiddle

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddleCertified =====
section

/-! Additive actual-contact closure for a bounded zero-cap left-stationary
slice. Its sources are only staged; all named theorems require Lean compilation
and a standard-three axiom audit before acceptance. -/

namespace GeneralCK
open ZeroCapLeftStationaryThetaBracket
open ZeroCapLeftStationaryAnchorContacts
open ZeroCapLeftStationaryRadialSlopeIntervals
open ZeroCapLeftStationaryEntropyBounds
namespace ZeroCapLeftStationaryNarrowMiddleCertified

theorem theta1_lower :
    (121 / 100 : ℝ) ≤ e8Theta (3175 / 29184) :=
  radialSlope1_lower.trans
    (e8Theta_lower_of_contact_upper (by norm_num) (by norm_num)
      (by norm_num) contact1_upper)

theorem theta2_lower :
    (3 : ℝ) ≤ e8Theta (25 / 76) :=
  radialSlope2_lower.trans
    (e8Theta_lower_of_contact_upper (by norm_num) (by norm_num)
      (by norm_num) contact2_upper)

theorem theta3_upper :
    e8Theta (375 / 646) ≤ (417 / 100 : ℝ) :=
  (e8Theta_upper_of_contact_lower (by norm_num) (by norm_num)
    (by norm_num) contact3_lower).trans radialSlope3_upper

theorem no_left_stationary_in_narrow_middle {a b c : ℝ}
    (ha : 1 / 8 ≤ a) (ha' : a ≤ 129 / 1024)
    (hb : 129 / 1024 ≤ b) (hb' : b ≤ 65 / 512)
    (hc : 1 / 4 ≤ c) (hc' : c ≤ 5 / 16) :
    deriv (fun y => canonicalPureGap a y (H a) (H b)) c ≠ 0 := by
  obtain ⟨hElower, hEupper, hBupper⟩ :=
    narrow_box_entropy_bounds ha ha' hb hb'
  exact ZeroCapLeftStationaryNarrowMiddle.no_stationary_of_three_theta_anchors
    ha ha' hb hb' hc hc' hElower hEupper hBupper
    theta1_lower theta2_lower theta3_upper

end ZeroCapLeftStationaryNarrowMiddleCertified

#print axioms GeneralCK.ZeroCapLeftStationaryNarrowMiddleCertified.theta1_lower
#print axioms GeneralCK.ZeroCapLeftStationaryNarrowMiddleCertified.theta2_lower
#print axioms GeneralCK.ZeroCapLeftStationaryNarrowMiddleCertified.theta3_upper
#print axioms GeneralCK.ZeroCapLeftStationaryNarrowMiddleCertified.no_left_stationary_in_narrow_middle

end GeneralCK

end


