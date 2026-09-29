-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryThetaBracketBridge
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryThetaBracketBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:58:12.293992+00:00
-- url     : https://prove2.me/theorems/3f6241b7-4a2d-42f1-80ab-d7dd338035bb
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryThetaBracketBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryThetaBracketBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryThetaBracketBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryThetaBracketBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryThetaBracketBridge.lean)

import Definitions.Def_CK_GeneralCK_PureGapMiddleDeterministic
import Definitions.Def_CK_GeneralCK_RadialContact
import Definitions.Def_CK_GeneralCK_RadialDerivatives

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryThetaBracketBridge =====
section

/-! Additive semantic bridge for source-only exact-rational stationary anchors.
It retains the actual radial contact and exact `e8Theta` derivative. -/

namespace GeneralCK
open Set
namespace ZeroCapLeftStationaryThetaBracket

theorem radialSlope_antitone : AntitoneOn radialSlope (Ioo (0 : ℝ) (1 / 2)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 (1 / 2))
  · intro v hv
    exact (hasDerivAt_radialSlope hv.1 hv.2).continuousAt.continuousWithinAt
  · intro v hv
    exact (hasDerivAt_radialSlope (interior_subset hv).1
      (interior_subset hv).2).hasDerivWithinAt
  · intro v hv
    have hv' := interior_subset hv
    have hhn : 0 ≤ Certificates.Mixed.hn v := by
      rw [Certificates.Mixed.hn_eq_H_mul_log]
      exact mul_nonneg (H_nonneg hv'.1.le (by linarith [hv'.2])) log_two_pos.le
    have hgap : 0 ≤ 2 * Certificates.Mixed.kap v - (1 - 2 * v)^2 :=
      kap_sq_gap_nonneg hv'.1 (by linarith [hv'.2])
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hhn) hgap) (by positivity)

theorem e8Theta_lower_of_contact_upper {x v : ℝ}
    (hx : 0 < x) (hv : 0 < v) (hv' : v < 1 / 2)
    (hcontact : radialContact (2 * x) 1 ≤ v) :
    radialSlope v ≤ e8Theta x := by
  have hcv : radialContact (2 * x) 1 ∈ Ioo (0 : ℝ) (1 / 2) :=
    ⟨radialContact_pos (by positivity) (by norm_num),
      radialContact_lt_half (by positivity) (by norm_num)⟩
  have h := radialSlope_antitone hcv ⟨hv, hv'⟩ hcontact
  unfold e8Theta
  rw [deriv_F_radius_slope (by positivity) (by norm_num)]
  exact h

theorem e8Theta_upper_of_contact_lower {x v : ℝ}
    (hx : 0 < x) (hv : 0 < v) (hv' : v < 1 / 2)
    (hcontact : v ≤ radialContact (2 * x) 1) :
    e8Theta x ≤ radialSlope v := by
  have hcv : radialContact (2 * x) 1 ∈ Ioo (0 : ℝ) (1 / 2) :=
    ⟨radialContact_pos (by positivity) (by norm_num),
      radialContact_lt_half (by positivity) (by norm_num)⟩
  have h := radialSlope_antitone ⟨hv, hv'⟩ hcv hcontact
  unfold e8Theta
  rw [deriv_F_radius_slope (by positivity) (by norm_num)]
  exact h

theorem contact_upper_of_entropy_lower {x v e : ℝ}
    (hx : 0 < x) (hv : 0 ≤ v) (hv' : v ≤ 1 / 2)
    (he : e ≤ H v) (hres : 1 - 2 * v ≤ 2 * x * e) :
    radialContact (2 * x) 1 ≤ v := by
  apply (radialContact_le_iff (by positivity) (by norm_num) hv hv').2
  have hm := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx.le)
  nlinarith only [hm, hres]

theorem contact_lower_of_entropy_upper {x v e : ℝ}
    (hx : 0 < x) (hv : 0 ≤ v) (hv' : v ≤ 1 / 2)
    (he : H v ≤ e) (hres : 2 * x * e ≤ 1 - 2 * v) :
    v ≤ radialContact (2 * x) 1 := by
  apply (le_radialContact_iff (by positivity) (by norm_num) hv hv').2
  have hm := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx.le)
  nlinarith only [hm, hres]

end ZeroCapLeftStationaryThetaBracket

#print axioms GeneralCK.ZeroCapLeftStationaryThetaBracket.radialSlope_antitone
#print axioms GeneralCK.ZeroCapLeftStationaryThetaBracket.e8Theta_lower_of_contact_upper
#print axioms GeneralCK.ZeroCapLeftStationaryThetaBracket.e8Theta_upper_of_contact_lower

end GeneralCK

end


