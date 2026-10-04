-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_c03
-- name    : CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_c03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T06:42:58.163702+00:00
-- url     : https://prove2.me/theorems/d82f7989-9bd1-4831-b27c-0ada651b1422
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage030)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage030)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage030)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage030) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointFamily/Coverage000 (proof part of coverage030).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0484__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0487__4

namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage030_part_03 {a z : ℝ} (ha : Bounds (33/100) (173/500) a)
    (hz : Bounds (1/1000) (1/100) z) (h0 : a≤(169/500:ℝ)) (h1 : ¬ (a≤(167/500:ℝ))) (h5 : ¬ (a≤(42/125:ℝ))) :
    0<curvature a (a*z) := by
  by_cases h7 : a≤(337/1000:ℝ)
  · exact Cell0486.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
  · exact Cell0487.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz

end GeneralCK.Certificates.ReflectionMidpointFamily


