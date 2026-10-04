-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate_t01
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate_t01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T23:03:10.102788+00:00
-- url     : https://prove2.me/theorems/80112c62-0669-4a0e-bca4-f7e9ee86c351
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem full_midpoint_next_strip_t01 {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (1/100) (1/20) z) (h0 : a≤(291/1000:ℝ)) (h1 : ¬ (a≤(479/2500:ℝ))) :
    0<curvature a (a*z) := by
  by_cases h14 : a≤(47/200:ℝ)
  · by_cases h15 : a≤(203/1000:ℝ)
    · by_cases h16 : a≤(487/2500:ℝ)
      · exact coverage013 ⟨(le_of_lt (lt_of_not_ge h1)),h16⟩ hz
      · by_cases h17 : a≤(99/500:ℝ)
        · exact coverage014 ⟨(le_of_lt (lt_of_not_ge h16)),h17⟩ hz
        · exact coverage015 ⟨(le_of_lt (lt_of_not_ge h17)),h15⟩ hz
    · by_cases h18 : a≤(219/1000:ℝ)
      · by_cases h19 : a≤(211/1000:ℝ)
        · exact coverage016 ⟨(le_of_lt (lt_of_not_ge h15)),h19⟩ hz
        · exact coverage017 ⟨(le_of_lt (lt_of_not_ge h19)),h18⟩ hz
      · by_cases h20 : a≤(227/1000:ℝ)
        · exact coverage018 ⟨(le_of_lt (lt_of_not_ge h18)),h20⟩ hz
        · exact coverage019 ⟨(le_of_lt (lt_of_not_ge h20)),h14⟩ hz
  · by_cases h21 : a≤(259/1000:ℝ)
    · by_cases h22 : a≤(243/1000:ℝ)
      · exact coverage020 ⟨(le_of_lt (lt_of_not_ge h14)),h22⟩ hz
      · by_cases h23 : a≤(251/1000:ℝ)
        · exact coverage021 ⟨(le_of_lt (lt_of_not_ge h22)),h23⟩ hz
        · exact coverage022 ⟨(le_of_lt (lt_of_not_ge h23)),h21⟩ hz
    · by_cases h24 : a≤(11/40:ℝ)
      · by_cases h25 : a≤(267/1000:ℝ)
        · exact coverage023 ⟨(le_of_lt (lt_of_not_ge h21)),h25⟩ hz
        · exact coverage024 ⟨(le_of_lt (lt_of_not_ge h25)),h24⟩ hz
      · by_cases h26 : a≤(283/1000:ℝ)
        · exact coverage025 ⟨(le_of_lt (lt_of_not_ge h24)),h26⟩ hz
        · exact coverage026 ⟨(le_of_lt (lt_of_not_ge h26)),h0⟩ hz

end GeneralCK.Certificates.ReflectionMidpointNextFamily


