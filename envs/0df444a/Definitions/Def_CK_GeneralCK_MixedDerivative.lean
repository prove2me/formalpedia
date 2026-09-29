-- Prove2me | Definitions.Def_CK_GeneralCK_MixedDerivative
-- name    : CK_GeneralCK_MixedDerivative
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:36:33.371947+00:00
-- url     : https://prove2.me/theorems/a520caee-de00-4766-8723-53de8781227d
-- title:
--   Courtade–Kumar proof module `GeneralCK.MixedDerivative` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.MixedDerivative` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.MixedDerivative` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.MixedDerivative (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/MixedDerivative.lean)

import Definitions.Def_CK_GeneralCK_RadialDerivatives
import Definitions.Def_CK_GeneralCK_MixedTails
import Definitions.Def_CK_GeneralCK_Certificates_MixedCertificate

namespace GeneralCK

/-- The explicit scalar profile is bounded over its entire contact domain.
The compact part is checked from 105 original closed intervals; the tails are analytic. -/
theorem mixed_profile_global {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    Certificates.Mixed.profile v ≤ 13 / 6 := by
  by_cases hl : v ≤ 1 / 22
  · exact Certificates.Mixed.Tails.profile_left_tail hv hl
  · by_cases hr : 1 / 3 ≤ v
    · exact Certificates.Mixed.Tails.profile_right_tail hr hv'
    · exact Certificates.Mixed.mixed_compact v (le_of_not_ge hl) (le_of_not_ge hr)

/-- The manuscript's global mixed derivative bound, including both analytic tails.
Every numerical premise has been discharged by kernel-checked rational witnesses. -/
theorem global_mixed_derivative_bound {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * deriv (deriv (fun r => F r h)) z ≤ 13 / 6 := by
  rw [radius_mul_deriv2_F_eq_profile hz hh]
  exact mixed_profile_global (radialContact_pos hz hh) (radialContact_lt_half hz hh)

end GeneralCK


