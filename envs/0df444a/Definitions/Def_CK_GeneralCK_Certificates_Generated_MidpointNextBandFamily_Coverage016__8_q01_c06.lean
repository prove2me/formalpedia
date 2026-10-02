-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q01_c06
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q01_c06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T20:06:01.172985+00:00
-- url     : https://prove2.me/theorems/7dbca3ba-ca78-44cd-a5e8-32a37617a0f3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (proof part of coverage017)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (proof part of coverage017)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (proof part of coverage017)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (proof part of coverage017) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage016 (proof part of coverage017).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0283__4

namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage017_part_06 {a z : ℝ} (ha : Bounds (113/500) (489/2000) a)
    (hz : Bounds (406621/5000000) (17/200) z) (h0 : ¬ (a ≤ (117/500:ℝ))) (h8 : ¬ (a ≤ (477/2000:ℝ))) (h12 : a ≤ (483/2000:ℝ)) :
    0 < curvature a (a*z) := by
  by_cases h13 : a ≤ (6/25:ℝ)
  · exact Cell0284.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
  · exact Cell0285.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz

end GeneralCK.Certificates.ReflectionMidpointNextBandFamily


