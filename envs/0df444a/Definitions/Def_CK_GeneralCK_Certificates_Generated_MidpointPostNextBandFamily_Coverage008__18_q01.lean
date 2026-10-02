-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q01
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T05:48:54.946086+00:00
-- url     : https://prove2.me/theorems/47513e0f-dabb-4762-981d-95eeae1d6113
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009,…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage025) (piece 2 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage025) (piece 2 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage025) (piece 2 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage008 (+17 modules: GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage015, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage016, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage023, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage024, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage025) (piece 2 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0142__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0145__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0149__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0153__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0157__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage009 {a z : ℝ} (ha : Bounds (102/625) (104/625) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (103/625:ℝ)
  · by_cases h1 : a ≤ (41/250:ℝ)
    · by_cases h2 : a ≤ (409/2500:ℝ)
      · by_cases h3 : a ≤ (817/5000:ℝ)
        · exact Cell0144.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0145.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (819/5000:ℝ)
        · exact Cell0146.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0147.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (411/2500:ℝ)
      · by_cases h6 : a ≤ (821/5000:ℝ)
        · exact Cell0148.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0149.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (823/5000:ℝ)
        · exact Cell0150.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0151.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (207/1250:ℝ)
    · by_cases h9 : a ≤ (413/2500:ℝ)
      · by_cases h10 : a ≤ (33/200:ℝ)
        · exact Cell0152.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0153.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (827/5000:ℝ)
        · exact Cell0154.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0155.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (83/500:ℝ)
      · by_cases h13 : a ≤ (829/5000:ℝ)
        · exact Cell0156.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0157.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (831/5000:ℝ)
        · exact Cell0158.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0159.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

end


