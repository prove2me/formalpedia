-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q15_c07
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q15_c07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T21:15:13.831538+00:00
-- url     : https://prove2.me/theorems/9d568d5e-e5db-40a3-85ab-c123548dd5c1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage023)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage023)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage023)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (proof part of coverage023) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage008 (proof part of coverage023).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0380__4

namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage023_part_07 {a z : ℝ} (ha : Bounds (169/500) (87/200) a)
    (hz : Bounds (17/200) (43/500) z) (h0 : ¬ (a ≤ (377/1000:ℝ))) (h8 : ¬ (a ≤ (403/1000:ℝ))) (h12 : ¬ (a ≤ (209/500:ℝ))) :
    0 < curvature a (a*z) := by
  by_cases h14 : a ≤ (213/500:ℝ)
  · exact Cell0382.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
  · exact Cell0383.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz

end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily


