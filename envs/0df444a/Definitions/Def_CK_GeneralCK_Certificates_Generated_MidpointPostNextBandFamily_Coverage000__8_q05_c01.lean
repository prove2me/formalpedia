-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05_c01
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05_c01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:18:55.793985+00:00
-- url     : https://prove2.me/theorems/0417a653-c218-4166-bc26-b5a2a27a213c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (proof part of coverage005)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (proof part of coverage005)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (proof part of coverage005)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (proof part of coverage005) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage000 (proof part of coverage005).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0082__2

namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage005_part_01 {a z : ℝ} (ha : Bounds (1563/10000) (1579/10000) a)
    (hz : Bounds (17/200) (43/500) z) (h0 : a ≤ (1571/10000:ℝ)) (h1 : a ≤ (1567/10000:ℝ)) (h2 : ¬ (a ≤ (313/2000:ℝ))) :
    0 < curvature a (a*z) := by
  by_cases h4 : a ≤ (783/5000:ℝ)
  · exact Cell0082.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
  · exact Cell0083.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz

end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily


