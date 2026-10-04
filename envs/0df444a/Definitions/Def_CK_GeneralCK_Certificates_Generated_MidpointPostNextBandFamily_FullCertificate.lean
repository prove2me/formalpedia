-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_FullCertificate
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_FullCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T06:37:25.970987+00:00
-- url     : https://prove2.me/theorems/8117a336-3cd0-45e3-99ea-ea50c9ca443c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.FullCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.FullCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.FullCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.FullCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/FullCertificate.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18

-- ===== source module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.FullCertificate =====
section
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem full_midpoint_post_next_band {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (22/125:ℝ)
  · by_cases h1 : a ≤ (1579/10000:ℝ)
    · by_cases h2 : a ≤ (1531/10000:ℝ)
      · by_cases h3 : a ≤ (377/2500:ℝ)
        · exact coverage000 ⟨ha.1,h3⟩ hz
        · by_cases h4 : a ≤ (379/2500:ℝ)
          · exact coverage001 ⟨(le_of_lt (lt_of_not_ge h3)),h4⟩ hz
          · exact coverage002 ⟨(le_of_lt (lt_of_not_ge h4)),h2⟩ hz
      · by_cases h5 : a ≤ (1547/10000:ℝ)
        · exact coverage003 ⟨(le_of_lt (lt_of_not_ge h2)),h5⟩ hz
        · by_cases h6 : a ≤ (1563/10000:ℝ)
          · exact coverage004 ⟨(le_of_lt (lt_of_not_ge h5)),h6⟩ hz
          · exact coverage005 ⟨(le_of_lt (lt_of_not_ge h6)),h1⟩ hz
    · by_cases h7 : a ≤ (102/625:ℝ)
      · by_cases h8 : a ≤ (319/2000:ℝ)
        · exact coverage006 ⟨(le_of_lt (lt_of_not_ge h1)),h8⟩ hz
        · by_cases h9 : a ≤ (1611/10000:ℝ)
          · exact coverage007 ⟨(le_of_lt (lt_of_not_ge h8)),h9⟩ hz
          · exact coverage008 ⟨(le_of_lt (lt_of_not_ge h9)),h7⟩ hz
      · by_cases h10 : a ≤ (106/625:ℝ)
        · by_cases h11 : a ≤ (104/625:ℝ)
          · exact coverage009 ⟨(le_of_lt (lt_of_not_ge h7)),h11⟩ hz
          · exact coverage010 ⟨(le_of_lt (lt_of_not_ge h11)),h10⟩ hz
        · by_cases h12 : a ≤ (108/625:ℝ)
          · exact coverage011 ⟨(le_of_lt (lt_of_not_ge h10)),h12⟩ hz
          · exact coverage012 ⟨(le_of_lt (lt_of_not_ge h12)),h0⟩ hz
  · by_cases h13 : a ≤ (109/500:ℝ)
    · by_cases h14 : a ≤ (961/5000:ℝ)
      · by_cases h15 : a ≤ (897/5000:ℝ)
        · exact coverage013 ⟨(le_of_lt (lt_of_not_ge h0)),h15⟩ hz
        · by_cases h16 : a ≤ (929/5000:ℝ)
          · exact coverage014 ⟨(le_of_lt (lt_of_not_ge h15)),h16⟩ hz
          · exact coverage015 ⟨(le_of_lt (lt_of_not_ge h16)),h14⟩ hz
      · by_cases h17 : a ≤ (201/1000:ℝ)
        · exact coverage016 ⟨(le_of_lt (lt_of_not_ge h14)),h17⟩ hz
        · by_cases h18 : a ≤ (209/1000:ℝ)
          · exact coverage017 ⟨(le_of_lt (lt_of_not_ge h17)),h18⟩ hz
          · exact coverage018 ⟨(le_of_lt (lt_of_not_ge h18)),h13⟩ hz
    · by_cases h19 : a ≤ (289/1000:ℝ)
      · by_cases h20 : a ≤ (117/500:ℝ)
        · exact coverage019 ⟨(le_of_lt (lt_of_not_ge h13)),h20⟩ hz
        · by_cases h21 : a ≤ (511/2000:ℝ)
          · exact coverage020 ⟨(le_of_lt (lt_of_not_ge h20)),h21⟩ hz
          · exact coverage021 ⟨(le_of_lt (lt_of_not_ge h21)),h19⟩ hz
      · by_cases h22 : a ≤ (87/200:ℝ)
        · by_cases h23 : a ≤ (169/500:ℝ)
          · exact coverage022 ⟨(le_of_lt (lt_of_not_ge h19)),h23⟩ hz
          · exact coverage023 ⟨(le_of_lt (lt_of_not_ge h23)),h22⟩ hz
        · by_cases h24 : a ≤ (82/125:ℝ)
          · exact coverage024 ⟨(le_of_lt (lt_of_not_ge h22)),h24⟩ hz
          · exact coverage025 ⟨(le_of_lt (lt_of_not_ge h24)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

end


