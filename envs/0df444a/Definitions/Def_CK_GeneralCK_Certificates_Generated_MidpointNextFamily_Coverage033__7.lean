-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T04:50:11.099975+00:00
-- url     : https://prove2.me/theorems/ad094763-c99d-4320-b784-900835f20619
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certif…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage033 (+6 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage034, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage035, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage036, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage037, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage038, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage039).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7_q05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0623__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0627__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0631__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0635__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0639__3

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage039 {a z : ℝ} (ha : Bounds (237/500) (49/100) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(241/500:ℝ)
  · by_cases h1 : a≤(239/500:ℝ)
    · by_cases h2 : a≤(119/250:ℝ)
      · by_cases h3 : a≤(19/40:ℝ)
        · exact Cell0624.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0625.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(477/1000:ℝ)
        · exact Cell0626.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0627.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(12/25:ℝ)
      · by_cases h6 : a≤(479/1000:ℝ)
        · exact Cell0628.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0629.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(481/1000:ℝ)
        · exact Cell0630.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0631.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(243/500:ℝ)
    · by_cases h9 : a≤(121/250:ℝ)
      · by_cases h10 : a≤(483/1000:ℝ)
        · exact Cell0632.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0633.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(97/200:ℝ)
        · exact Cell0634.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0635.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(61/125:ℝ)
      · by_cases h13 : a≤(487/1000:ℝ)
        · exact Cell0636.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0637.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(489/1000:ℝ)
        · exact Cell0638.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0639.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


