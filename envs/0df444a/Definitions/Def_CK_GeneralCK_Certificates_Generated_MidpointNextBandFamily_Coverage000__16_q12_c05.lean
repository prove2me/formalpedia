-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q12_c05
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q12_c05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T06:22:35.546134+00:00
-- url     : https://prove2.me/theorems/5d1669ef-0b3e-4795-a308-4d1aa784d0c2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (proof part of coverage012)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (proof part of coverage012)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (proof part of coverage012)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (proof part of coverage012) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage000 (proof part of coverage012).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0201__4

namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage012_part_05 {a z : ℝ} (ha : Bounds (113/625) (117/625) a)
    (hz : Bounds (406621/5000000) (17/200) z) (h0 : ¬ (a ≤ (23/125:ℝ))) (h8 : a ≤ (116/625:ℝ)) (h9 : ¬ (a ≤ (231/1250:ℝ))) :
    0 < curvature a (a*z) := by
  by_cases h11 : a ≤ (463/2500:ℝ)
  · exact Cell0202.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
  · exact Cell0203.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz

end GeneralCK.Certificates.ReflectionMidpointNextBandFamily


