-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7_q03
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7_q03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T01:49:39.251151+00:00
-- url     : https://prove2.me/theorems/1d78a5f3-2312-4c5d-aecf-5e54924690cd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certif…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039) (piece 4 of 7)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039) (piece 4 of 7)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039) (piece 4 of 7) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage033 (+6 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage034, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage035, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage036, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage037, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage038, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage039) (piece 4 of 7).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7_q02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0573__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0577__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0580__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0583__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0586__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0590__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage036 {a z : ℝ} (ha : Bounds (213/500) (221/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(217/500:ℝ)
  · by_cases h1 : a≤(43/100:ℝ)
    · by_cases h2 : a≤(107/250:ℝ)
      · by_cases h3 : a≤(427/1000:ℝ)
        · exact Cell0576.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0577.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(429/1000:ℝ)
        · exact Cell0578.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0579.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(54/125:ℝ)
      · by_cases h6 : a≤(431/1000:ℝ)
        · exact Cell0580.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0581.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(433/1000:ℝ)
        · exact Cell0582.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0583.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(219/500:ℝ)
    · by_cases h9 : a≤(109/250:ℝ)
      · by_cases h10 : a≤(87/200:ℝ)
        · exact Cell0584.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0585.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(437/1000:ℝ)
        · exact Cell0586.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0587.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(11/25:ℝ)
      · by_cases h13 : a≤(439/1000:ℝ)
        · exact Cell0588.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0589.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(441/1000:ℝ)
        · exact Cell0590.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0591.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


