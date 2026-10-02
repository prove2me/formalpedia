-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q02
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T20:26:27.851405+00:00
-- url     : https://prove2.me/theorems/1c7f5c7a-58f4-4c8e-abe1-c32849a71b49
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, General…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage015) (piece 3 of 16)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage015) (piece 3 of 16)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage015) (piece 3 of 16) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage000 (+15 modules: GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage007, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage008, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage015) (piece 3 of 16).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0030__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0034__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0038__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0041__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0043__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0046__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage002 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage002 {a z : ℝ} (ha : Bounds (383/2500) (387/2500) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (77/500:ℝ)
  · by_cases h1 : a ≤ (96/625:ℝ)
    · by_cases h2 : a ≤ (767/5000:ℝ)
      · by_cases h3 : a ≤ (1533/10000:ℝ)
        · exact Cell0032.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0033.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (307/2000:ℝ)
        · exact Cell0034.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0035.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (769/5000:ℝ)
      · by_cases h6 : a ≤ (1537/10000:ℝ)
        · exact Cell0036.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0037.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (1539/10000:ℝ)
        · exact Cell0038.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0039.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (193/1250:ℝ)
    · by_cases h9 : a ≤ (771/5000:ℝ)
      · by_cases h10 : a ≤ (1541/10000:ℝ)
        · exact Cell0040.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0041.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (1543/10000:ℝ)
        · exact Cell0042.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0043.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (773/5000:ℝ)
      · by_cases h13 : a ≤ (309/2000:ℝ)
        · exact Cell0044.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0045.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (1547/10000:ℝ)
        · exact Cell0046.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0047.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

end


