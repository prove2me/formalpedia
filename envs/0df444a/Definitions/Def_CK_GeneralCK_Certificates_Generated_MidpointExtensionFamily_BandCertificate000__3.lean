-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_BandCertificate000__3
-- name    : CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_BandCertificate000__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T22:54:11.140982+00:00
-- url     : https://prove2.me/theorems/167c3e7c-bf36-45da-808b-1e3f2dd3cd35
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate000 (+2 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate000 (+2 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate001, GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate002)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate000 (+2 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate001, GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate002)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate000 (+2 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate001, GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate002) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointExtensionFamily/BandCertificate000 (+2 modules: GeneralCK/Certificates/Generated/MidpointExtensionFamily/BandCertificate001, GeneralCK/Certificates/Generated/MidpointExtensionFamily/BandCertificate002).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage000__31
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23

-- ===== source module GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate000 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem bandcertificate000 {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (1/20) (81/1000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (479/2500:ℝ)
  · by_cases h1 : a ≤ (813/5000:ℝ)
    · by_cases h2 : a ≤ (781/5000:ℝ)
      · by_cases h3 : a ≤ (153/1000:ℝ)
        · exact coverage000 ⟨ha.1,h3⟩ hz
        · exact coverage001 ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (797/5000:ℝ)
        · exact coverage002 ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact coverage003 ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (106/625:ℝ)
      · by_cases h6 : a ≤ (829/5000:ℝ)
        · exact coverage004 ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact coverage005 ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (22/125:ℝ)
        · exact coverage006 ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · by_cases h8 : a ≤ (114/625:ℝ)
          · exact coverage007 ⟨(le_of_lt (lt_of_not_ge h7)),h8⟩ hz
          · exact coverage008 ⟨(le_of_lt (lt_of_not_ge h8)),h0⟩ hz
  · by_cases h9 : a ≤ (127/500:ℝ)
    · by_cases h10 : a ≤ (427/2000:ℝ)
      · by_cases h11 : a ≤ (101/500:ℝ)
        · exact coverage009 ⟨(le_of_lt (lt_of_not_ge h0)),h11⟩ hz
        · exact coverage010 ⟨(le_of_lt (lt_of_not_ge h11)),h10⟩ hz
      · by_cases h12 : a ≤ (459/2000:ℝ)
        · exact coverage011 ⟨(le_of_lt (lt_of_not_ge h10)),h12⟩ hz
        · exact coverage012 ⟨(le_of_lt (lt_of_not_ge h12)),h9⟩ hz
    · by_cases h13 : a ≤ (44/125:ℝ)
      · by_cases h14 : a ≤ (73/250:ℝ)
        · exact coverage013 ⟨(le_of_lt (lt_of_not_ge h9)),h14⟩ hz
        · exact coverage014 ⟨(le_of_lt (lt_of_not_ge h14)),h13⟩ hz
      · by_cases h15 : a ≤ (239/500:ℝ)
        · exact coverage015 ⟨(le_of_lt (lt_of_not_ge h13)),h15⟩ hz
        · by_cases h16 : a ≤ (163/200:ℝ)
          · exact coverage016 ⟨(le_of_lt (lt_of_not_ge h15)),h16⟩ hz
          · exact coverage017 ⟨(le_of_lt (lt_of_not_ge h16)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

end

-- ===== source module GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate001 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem bandcertificate001 {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (19/100:ℝ)
  · by_cases h1 : a ≤ (811/5000:ℝ)
    · by_cases h2 : a ≤ (779/5000:ℝ)
      · by_cases h3 : a ≤ (763/5000:ℝ)
        · exact coverage018 ⟨ha.1,h3⟩ hz
        · exact coverage019 ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (159/1000:ℝ)
        · exact coverage020 ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact coverage021 ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (843/5000:ℝ)
      · by_cases h6 : a ≤ (827/5000:ℝ)
        · exact coverage022 ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact coverage023 ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (7/40:ℝ)
        · exact coverage024 ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · by_cases h8 : a ≤ (907/5000:ℝ)
          · exact coverage025 ⟨(le_of_lt (lt_of_not_ge h7)),h8⟩ hz
          · exact coverage026 ⟨(le_of_lt (lt_of_not_ge h8)),h0⟩ hz
  · by_cases h9 : a ≤ (497/2000:ℝ)
    · by_cases h10 : a ≤ (421/2000:ℝ)
      · by_cases h11 : a ≤ (401/2000:ℝ)
        · exact coverage027 ⟨(le_of_lt (lt_of_not_ge h0)),h11⟩ hz
        · exact coverage028 ⟨(le_of_lt (lt_of_not_ge h11)),h10⟩ hz
      · by_cases h12 : a ≤ (453/2000:ℝ)
        · exact coverage029 ⟨(le_of_lt (lt_of_not_ge h10)),h12⟩ hz
        · exact coverage030 ⟨(le_of_lt (lt_of_not_ge h12)),h9⟩ hz
    · by_cases h13 : a ≤ (337/1000:ℝ)
      · by_cases h14 : a ≤ (283/1000:ℝ)
        · exact coverage031 ⟨(le_of_lt (lt_of_not_ge h9)),h14⟩ hz
        · exact coverage032 ⟨(le_of_lt (lt_of_not_ge h14)),h13⟩ hz
      · by_cases h15 : a ≤ (223/500:ℝ)
        · exact coverage033 ⟨(le_of_lt (lt_of_not_ge h13)),h15⟩ hz
        · by_cases h16 : a ≤ (361/500:ℝ)
          · exact coverage034 ⟨(le_of_lt (lt_of_not_ge h15)),h16⟩ hz
          · exact coverage035 ⟨(le_of_lt (lt_of_not_ge h16)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

end

-- ===== source module GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate002 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem bandcertificate002 {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (19/100:ℝ)
  · by_cases h1 : a ≤ (811/5000:ℝ)
    · by_cases h2 : a ≤ (779/5000:ℝ)
      · by_cases h3 : a ≤ (763/5000:ℝ)
        · exact coverage036 ⟨ha.1,h3⟩ hz
        · exact coverage037 ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (159/1000:ℝ)
        · exact coverage038 ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact coverage039 ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (843/5000:ℝ)
      · by_cases h6 : a ≤ (827/5000:ℝ)
        · exact coverage040 ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact coverage041 ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (7/40:ℝ)
        · exact coverage042 ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · by_cases h8 : a ≤ (907/5000:ℝ)
          · exact coverage043 ⟨(le_of_lt (lt_of_not_ge h7)),h8⟩ hz
          · exact coverage044 ⟨(le_of_lt (lt_of_not_ge h8)),h0⟩ hz
  · by_cases h9 : a ≤ (497/2000:ℝ)
    · by_cases h10 : a ≤ (421/2000:ℝ)
      · by_cases h11 : a ≤ (401/2000:ℝ)
        · exact coverage045 ⟨(le_of_lt (lt_of_not_ge h0)),h11⟩ hz
        · exact coverage046 ⟨(le_of_lt (lt_of_not_ge h11)),h10⟩ hz
      · by_cases h12 : a ≤ (453/2000:ℝ)
        · exact coverage047 ⟨(le_of_lt (lt_of_not_ge h10)),h12⟩ hz
        · exact coverage048 ⟨(le_of_lt (lt_of_not_ge h12)),h9⟩ hz
    · by_cases h13 : a ≤ (337/1000:ℝ)
      · by_cases h14 : a ≤ (283/1000:ℝ)
        · exact coverage049 ⟨(le_of_lt (lt_of_not_ge h9)),h14⟩ hz
        · exact coverage050 ⟨(le_of_lt (lt_of_not_ge h14)),h13⟩ hz
      · by_cases h15 : a ≤ (223/500:ℝ)
        · exact coverage051 ⟨(le_of_lt (lt_of_not_ge h13)),h15⟩ hz
        · by_cases h16 : a ≤ (361/500:ℝ)
          · exact coverage052 ⟨(le_of_lt (lt_of_not_ge h15)),h16⟩ hz
          · exact coverage053 ⟨(le_of_lt (lt_of_not_ge h16)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

end


