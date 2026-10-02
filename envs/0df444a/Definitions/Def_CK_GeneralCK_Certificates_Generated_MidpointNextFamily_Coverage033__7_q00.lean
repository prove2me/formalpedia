-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7_q00
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T18:51:32.733257+00:00
-- url     : https://prove2.me/theorems/659850a7-558d-4469-939d-10d0aa42bb72
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certif…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039) (piece 1 of 7)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039) (piece 1 of 7)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039) (piece 1 of 7) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage033 (+6 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage034, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage035, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage036, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage037, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage038, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage039) (piece 1 of 7).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0528__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0532__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0536__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0540__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0543__3

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage033 {a z : ℝ} (ha : Bounds (189/500) (197/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(193/500:ℝ)
  · by_cases h1 : a≤(191/500:ℝ)
    · by_cases h2 : a≤(19/50:ℝ)
      · by_cases h3 : a≤(379/1000:ℝ)
        · exact Cell0528.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0529.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(381/1000:ℝ)
        · exact Cell0530.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0531.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(48/125:ℝ)
      · by_cases h6 : a≤(383/1000:ℝ)
        · exact Cell0532.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0533.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(77/200:ℝ)
        · exact Cell0534.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0535.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(39/100:ℝ)
    · by_cases h9 : a≤(97/250:ℝ)
      · by_cases h10 : a≤(387/1000:ℝ)
        · exact Cell0536.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0537.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(389/1000:ℝ)
        · exact Cell0538.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0539.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(49/125:ℝ)
      · by_cases h13 : a≤(391/1000:ℝ)
        · exact Cell0540.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0541.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(393/1000:ℝ)
        · exact Cell0542.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0543.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


