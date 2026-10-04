-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_FullCertificate
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_FullCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:26:27.36504+00:00
-- url     : https://prove2.me/theorems/ef6f5730-68b4-4e1a-b0f5-6f78e4ae1166
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.FullCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.FullCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.FullCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.FullCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/FullCertificate.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextBandFamily.FullCertificate =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem full_midpoint_next_band {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (113/625:ℝ)
  · by_cases h1 : a ≤ (399/2500:ℝ)
    · by_cases h2 : a ≤ (387/2500:ℝ)
      · by_cases h3 : a ≤ (379/2500:ℝ)
        · exact coverage000 ⟨ha.1,h3⟩ hz
        · by_cases h4 : a ≤ (383/2500:ℝ)
          · exact coverage001 ⟨(le_of_lt (lt_of_not_ge h3)),h4⟩ hz
          · exact coverage002 ⟨(le_of_lt (lt_of_not_ge h4)),h2⟩ hz
      · by_cases h5 : a ≤ (391/2500:ℝ)
        · exact coverage003 ⟨(le_of_lt (lt_of_not_ge h2)),h5⟩ hz
        · by_cases h6 : a ≤ (79/500:ℝ)
          · exact coverage004 ⟨(le_of_lt (lt_of_not_ge h5)),h6⟩ hz
          · exact coverage005 ⟨(le_of_lt (lt_of_not_ge h6)),h1⟩ hz
    · by_cases h7 : a ≤ (423/2500:ℝ)
      · by_cases h8 : a ≤ (407/2500:ℝ)
        · exact coverage006 ⟨(le_of_lt (lt_of_not_ge h1)),h8⟩ hz
        · by_cases h9 : a ≤ (83/500:ℝ)
          · exact coverage007 ⟨(le_of_lt (lt_of_not_ge h8)),h9⟩ hz
          · exact coverage008 ⟨(le_of_lt (lt_of_not_ge h9)),h7⟩ hz
      · by_cases h10 : a ≤ (431/2500:ℝ)
        · exact coverage009 ⟨(le_of_lt (lt_of_not_ge h7)),h10⟩ hz
        · by_cases h11 : a ≤ (439/2500:ℝ)
          · exact coverage010 ⟨(le_of_lt (lt_of_not_ge h10)),h11⟩ hz
          · exact coverage011 ⟨(le_of_lt (lt_of_not_ge h11)),h0⟩ hz
  · by_cases h12 : a ≤ (489/2000:ℝ)
    · by_cases h13 : a ≤ (51/250:ℝ)
      · by_cases h14 : a ≤ (117/625:ℝ)
        · exact coverage012 ⟨(le_of_lt (lt_of_not_ge h0)),h14⟩ hz
        · by_cases h15 : a ≤ (39/200:ℝ)
          · exact coverage013 ⟨(le_of_lt (lt_of_not_ge h14)),h15⟩ hz
          · exact coverage014 ⟨(le_of_lt (lt_of_not_ge h15)),h13⟩ hz
      · by_cases h16 : a ≤ (53/250:ℝ)
        · exact coverage015 ⟨(le_of_lt (lt_of_not_ge h13)),h16⟩ hz
        · by_cases h17 : a ≤ (113/500:ℝ)
          · exact coverage016 ⟨(le_of_lt (lt_of_not_ge h16)),h17⟩ hz
          · exact coverage017 ⟨(le_of_lt (lt_of_not_ge h17)),h12⟩ hz
    · by_cases h18 : a ≤ (393/1000:ℝ)
      · by_cases h19 : a ≤ (109/400:ℝ)
        · exact coverage018 ⟨(le_of_lt (lt_of_not_ge h12)),h19⟩ hz
        · by_cases h20 : a ≤ (79/250:ℝ)
          · exact coverage019 ⟨(le_of_lt (lt_of_not_ge h19)),h20⟩ hz
          · exact coverage020 ⟨(le_of_lt (lt_of_not_ge h20)),h18⟩ hz
      · by_cases h21 : a ≤ (141/250:ℝ)
        · exact coverage021 ⟨(le_of_lt (lt_of_not_ge h18)),h21⟩ hz
        · by_cases h22 : a ≤ (499/500:ℝ)
          · exact coverage022 ⟨(le_of_lt (lt_of_not_ge h21)),h22⟩ hz
          · exact coverage023 ⟨(le_of_lt (lt_of_not_ge h22)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

end


