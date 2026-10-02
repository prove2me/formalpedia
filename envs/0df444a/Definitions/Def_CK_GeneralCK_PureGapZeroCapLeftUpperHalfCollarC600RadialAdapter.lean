-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarC600RadialAdapter
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarC600RadialAdapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T14:26:07.632139+00:00
-- url     : https://prove2.me/theorems/2b3b1c92-155c-4746-9584-0db34147e740
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarC600RadialAdapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarC600RadialAdapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarC600RadialAdapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperHalfCollarC600RadialAdapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperHalfCollarC600RadialAdapter.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarQuartic

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperHalfCollarC600RadialAdapter =====
section

/-!
Conditional transfer from a uniform C=600 estimate of the *actual radial
expression* to the strict left-upper half-collar canonical gap. The
radial estimate remains an explicit premise.
-/

namespace GeneralCK

theorem leftUpper_halfCollar_nonneg_of_radial_C600
    {z lambda : ℝ}
    (hz : 0 < z) (hzmax : z ≤ 1 / 64)
    (hlambda : 0 < lambda) (hlambda1 : lambda < 1)
    (habs :
      |(interiorCost (1 / 2 - z) (1 / 2 - lambda * z) +
          2 * F (1 / 2 - (1 / 2 - z))
            ((H (1 / 2 - z) + H (1 / 2 - lambda * z)) / 2) -
          F ((1 / 2 - lambda * z) - (1 / 2 - z))
            ((H (1 / 2 - z) + H (1 / 2 - lambda * z)) / 2) -
          eta ((H (1 / 2 - z) + H (1 / 2 - lambda * z)) / 2) +
          eta (H (1 / 2 - lambda * z)) / 2) -
        z ^ 4 * leftUpperQuarticCoefficient (Real.log 2) lambda| ≤
      600 * z ^ 6) :
    0 ≤ canonicalPureGap (1 / 2 - z) (1 / 2)
      (H (1 / 2 - z)) (H (1 / 2 - lambda * z)) := by
  have ha : 0 < 1 / 2 - z := by linarith
  have hab : 1 / 2 - z < 1 / 2 - lambda * z := by
    nlinarith [mul_lt_mul_of_pos_right hlambda1 hz]
  have hb : 1 / 2 - lambda * z < 1 / 2 := by
    nlinarith [mul_pos hlambda hz]
  have hRad := canonicalPureGap_leftUpper_radial_eq ha hab hb
  have hlow := (abs_le.mp habs).1
  apply leftUpper_halfCollar_nonneg_of_remainder
    hz hzmax (by norm_num) (by norm_num : (600 : ℝ) * (1 / 64) ^ 2 ≤ 35 / 48)
  rw [hRad]
  linarith

#print axioms leftUpper_halfCollar_nonneg_of_radial_C600

end GeneralCK

end


