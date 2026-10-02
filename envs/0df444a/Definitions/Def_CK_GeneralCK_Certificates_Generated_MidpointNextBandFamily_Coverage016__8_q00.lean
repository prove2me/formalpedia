-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q00
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:06:37.037993+00:00
-- url     : https://prove2.me/theorems/d4482889-70b7-4376-bfe1-91f2c56b8c33
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralC…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 1 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 1 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 1 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage016 (+7 modules: GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage023) (piece 1 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0256__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0259__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0263__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0267__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0271__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage016 {a z : ℝ} (ha : Bounds (53/250) (113/500) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (109/500:ℝ)
  · by_cases h1 : a ≤ (107/500:ℝ)
    · by_cases h2 : a ≤ (213/1000:ℝ)
      · by_cases h3 : a ≤ (17/80:ℝ)
        · exact Cell0256.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0257.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (427/2000:ℝ)
        · exact Cell0258.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0259.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (27/125:ℝ)
      · by_cases h6 : a ≤ (43/200:ℝ)
        · exact Cell0260.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0261.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (217/1000:ℝ)
        · exact Cell0262.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0263.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (111/500:ℝ)
    · by_cases h9 : a ≤ (11/50:ℝ)
      · by_cases h10 : a ≤ (219/1000:ℝ)
        · exact Cell0264.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0265.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (221/1000:ℝ)
        · exact Cell0266.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0267.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (28/125:ℝ)
      · by_cases h13 : a ≤ (223/1000:ℝ)
        · exact Cell0268.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0269.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (9/40:ℝ)
        · exact Cell0270.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0271.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

end


