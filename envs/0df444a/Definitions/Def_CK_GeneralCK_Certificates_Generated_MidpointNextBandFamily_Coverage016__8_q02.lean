-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q02
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:31:52.022577+00:00
-- url     : https://prove2.me/theorems/4cae4acb-a71a-410e-adf7-8f27da4e0821
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralC…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 3 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 3 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 3 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage016 (+7 modules: GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage023) (piece 3 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0287__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0291__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0295__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0299__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0303__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage018 {a z : ℝ} (ha : Bounds (489/2000) (109/400) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (513/2000:ℝ)
  · by_cases h1 : a ≤ (501/2000:ℝ)
    · by_cases h2 : a ≤ (99/400:ℝ)
      · by_cases h3 : a ≤ (123/500:ℝ)
        · exact Cell0288.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0289.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (249/1000:ℝ)
        · exact Cell0290.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0291.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (507/2000:ℝ)
      · by_cases h6 : a ≤ (63/250:ℝ)
        · exact Cell0292.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0293.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (51/200:ℝ)
        · exact Cell0294.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0295.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (529/2000:ℝ)
    · by_cases h9 : a ≤ (521/2000:ℝ)
      · by_cases h10 : a ≤ (517/2000:ℝ)
        · exact Cell0296.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0297.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (21/80:ℝ)
        · exact Cell0298.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0299.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (537/2000:ℝ)
      · by_cases h13 : a ≤ (533/2000:ℝ)
        · exact Cell0300.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0301.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (541/2000:ℝ)
        · exact Cell0302.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0303.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

end


