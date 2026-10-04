-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate_t02
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate_t02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T23:00:33.390369+00:00
-- url     : https://prove2.me/theorems/981e2b2e-69d7-486a-a168-16446eaaeb95
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem full_midpoint_next_strip_t02 {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (1/100) (1/20) z) (h0 : ¬ (a≤(291/1000:ℝ))) (h27 : a≤(49/100:ℝ)) :
    0<curvature a (a*z) := by
  by_cases h28 : a≤(189/500:ℝ)
  · by_cases h29 : a≤(33/100:ℝ)
    · by_cases h30 : a≤(299/1000:ℝ)
      · exact coverage027 ⟨(le_of_lt (lt_of_not_ge h0)),h30⟩ hz
      · by_cases h31 : a≤(157/500:ℝ)
        · exact coverage028 ⟨(le_of_lt (lt_of_not_ge h30)),h31⟩ hz
        · exact coverage029 ⟨(le_of_lt (lt_of_not_ge h31)),h29⟩ hz
    · by_cases h32 : a≤(173/500:ℝ)
      · exact coverage030 ⟨(le_of_lt (lt_of_not_ge h29)),h32⟩ hz
      · by_cases h33 : a≤(181/500:ℝ)
        · exact coverage031 ⟨(le_of_lt (lt_of_not_ge h32)),h33⟩ hz
        · exact coverage032 ⟨(le_of_lt (lt_of_not_ge h33)),h28⟩ hz
  · by_cases h34 : a≤(213/500:ℝ)
    · by_cases h35 : a≤(197/500:ℝ)
      · exact coverage033 ⟨(le_of_lt (lt_of_not_ge h28)),h35⟩ hz
      · by_cases h36 : a≤(41/100:ℝ)
        · exact coverage034 ⟨(le_of_lt (lt_of_not_ge h35)),h36⟩ hz
        · exact coverage035 ⟨(le_of_lt (lt_of_not_ge h36)),h34⟩ hz
    · by_cases h37 : a≤(229/500:ℝ)
      · by_cases h38 : a≤(221/500:ℝ)
        · exact coverage036 ⟨(le_of_lt (lt_of_not_ge h34)),h38⟩ hz
        · exact coverage037 ⟨(le_of_lt (lt_of_not_ge h38)),h37⟩ hz
      · by_cases h39 : a≤(237/500:ℝ)
        · exact coverage038 ⟨(le_of_lt (lt_of_not_ge h37)),h39⟩ hz
        · exact coverage039 ⟨(le_of_lt (lt_of_not_ge h39)),h27⟩ hz

end GeneralCK.Certificates.ReflectionMidpointNextFamily


