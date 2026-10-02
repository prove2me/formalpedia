-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q01_c01
-- name    : CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q01_c01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:36:11.648+00:00
-- url     : https://prove2.me/theorems/901c9887-c278-49ae-869d-7afc07fb802b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage001)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage001)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage001)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage001) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointFamily/Coverage000 (proof part of coverage001).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0018__3

namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage001_part_01 {a z : ℝ} (ha : Bounds (383/2500) (391/2500) a)
    (hz : Bounds (1/1000) (1/100) z) (h0 : a≤(387/2500:ℝ)) (h1 : a≤(77/500:ℝ)) (h2 : ¬ (a≤(96/625:ℝ))) :
    0<curvature a (a*z) := by
  by_cases h4 : a≤(769/5000:ℝ)
  · exact Cell0018.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
  · exact Cell0019.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz

end GeneralCK.Certificates.ReflectionMidpointFamily


