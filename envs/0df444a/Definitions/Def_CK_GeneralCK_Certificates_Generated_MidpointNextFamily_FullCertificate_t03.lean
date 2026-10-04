-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate_t03
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate_t03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T00:22:59.825515+00:00
-- url     : https://prove2.me/theorems/954d081b-cb3b-4b54-b84a-f3884d1262d1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.FullCertificate (proof part of full_midpoint_next_strip)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.FullCertificate (proof part of full_midpoint_next_strip)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.FullCertificate (proof part of full_midpoint_next_strip)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.FullCertificate (proof part of full_midpoint_next_strip) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/FullCertificate (proof part of full_midpoint_next_strip).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage040__13
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage053

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem full_midpoint_next_strip_t03 {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (1/100) (1/20) z) (h0 : ¬ (a≤(291/1000:ℝ))) (h27 : ¬ (a≤(49/100:ℝ))) :
    0<curvature a (a*z) := by
  by_cases h40 : a≤(88/125:ℝ)
  · by_cases h41 : a≤(72/125:ℝ)
    · by_cases h42 : a≤(64/125:ℝ)
      · exact coverage040 ⟨(le_of_lt (lt_of_not_ge h27)),h42⟩ hz
      · by_cases h43 : a≤(68/125:ℝ)
        · exact coverage041 ⟨(le_of_lt (lt_of_not_ge h42)),h43⟩ hz
        · exact coverage042 ⟨(le_of_lt (lt_of_not_ge h43)),h41⟩ hz
    · by_cases h44 : a≤(16/25:ℝ)
      · by_cases h45 : a≤(76/125:ℝ)
        · exact coverage043 ⟨(le_of_lt (lt_of_not_ge h41)),h45⟩ hz
        · exact coverage044 ⟨(le_of_lt (lt_of_not_ge h45)),h44⟩ hz
      · by_cases h46 : a≤(84/125:ℝ)
        · exact coverage045 ⟨(le_of_lt (lt_of_not_ge h44)),h46⟩ hz
        · exact coverage046 ⟨(le_of_lt (lt_of_not_ge h46)),h40⟩ hz
  · by_cases h47 : a≤(4/5:ℝ)
    · by_cases h48 : a≤(92/125:ℝ)
      · exact coverage047 ⟨(le_of_lt (lt_of_not_ge h40)),h48⟩ hz
      · by_cases h49 : a≤(96/125:ℝ)
        · exact coverage048 ⟨(le_of_lt (lt_of_not_ge h48)),h49⟩ hz
        · exact coverage049 ⟨(le_of_lt (lt_of_not_ge h49)),h47⟩ hz
    · by_cases h50 : a≤(477/500:ℝ)
      · by_cases h51 : a≤(22/25:ℝ)
        · exact coverage050 ⟨(le_of_lt (lt_of_not_ge h47)),h51⟩ hz
        · exact coverage051 ⟨(le_of_lt (lt_of_not_ge h51)),h50⟩ hz
      · by_cases h52 : a≤(493/500:ℝ)
        · exact coverage052 ⟨(le_of_lt (lt_of_not_ge h50)),h52⟩ hz
        · exact coverage053 ⟨(le_of_lt (lt_of_not_ge h52)),ha.2⟩ hz

end GeneralCK.Certificates.ReflectionMidpointNextFamily


