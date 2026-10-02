-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q04
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:44:06.792338+00:00
-- url     : https://prove2.me/theorems/26e4fa8c-1f49-41e8-9fbd-7a2cf1a7db0d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (+13 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage020, GeneralCK.Certi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (+13 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage030, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage031, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage032) (piece 5 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (+13 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage030, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage031, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage032) (piece 5 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (+13 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage030, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage031, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage032) (piece 5 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage019 (+13 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage023, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage024, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage025, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage026, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage027, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage028, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage029, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage030, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage031, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage032) (piece 5 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0367__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0371__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0375__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0379__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0383__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage023 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage023 {a z : ℝ} (ha : Bounds (259/1000) (267/1000) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(263/1000:ℝ)
  · by_cases h1 : a≤(261/1000:ℝ)
    · by_cases h2 : a≤(13/50:ℝ)
      · by_cases h3 : a≤(519/2000:ℝ)
        · exact Cell0368.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0369.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(521/2000:ℝ)
        · exact Cell0370.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0371.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(131/500:ℝ)
      · by_cases h6 : a≤(523/2000:ℝ)
        · exact Cell0372.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0373.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(21/80:ℝ)
        · exact Cell0374.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0375.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(53/200:ℝ)
    · by_cases h9 : a≤(33/125:ℝ)
      · by_cases h10 : a≤(527/2000:ℝ)
        · exact Cell0376.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0377.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(529/2000:ℝ)
        · exact Cell0378.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0379.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(133/500:ℝ)
      · by_cases h13 : a≤(531/2000:ℝ)
        · exact Cell0380.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0381.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(533/2000:ℝ)
        · exact Cell0382.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0383.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


