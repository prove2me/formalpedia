-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers
-- name    : CK_GeneralCK_Certificates_LowRatioFamilyHelpers
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:06:47.912253+00:00
-- url     : https://prove2.me/theorems/da1aaa1b-2bc8-4721-9852-cdeed2714778
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.LowRatioFamilyHelpers` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.LowRatioFamilyHelpers` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.LowRatioFamilyHelpers` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.LowRatioFamilyHelpers (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/LowRatioFamilyHelpers.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallRatioFormula

-- ===== source module GeneralCK.Certificates.LowRatioFamilyHelpers =====
section

namespace GeneralCK.Certificates.LowRatioFamily

theorem base_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    2*a/(1-a^2)^2 ≤ 2*b/(1-b^2)^2 := by
  have hb0 : 0 < b := ha.trans_le hab
  have hd : 0 < 1-b^2 := by nlinarith
  have hs : a^2 ≤ b^2 := (sq_le_sq₀ ha.le hb0.le).mpr hab
  have hda : 0 < 1-a^2 := by linarith
  have hsq : (1-b^2)^2 ≤ (1-a^2)^2 := (sq_le_sq₀ hd.le hda.le).mpr (by linarith)
  exact div_le_div₀ (by positivity) (by nlinarith) (sq_pos_of_pos hd) hsq

end GeneralCK.Certificates.LowRatioFamily

end


