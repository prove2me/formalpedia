-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_FullCertificate
-- name    : CK_GeneralCK_Certificates_Generated_MidpointFamily_FullCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T08:00:46.796986+00:00
-- url     : https://prove2.me/theorems/f71880d5-8f97-4dbe-8a42-3c5aff3e282b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointFamily.FullCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointFamily.FullCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointFamily.FullCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointFamily.FullCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointFamily/FullCertificate.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage031__23

-- ===== source module GeneralCK.Certificates.Generated.MidpointFamily.FullCertificate =====
section
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem full_midpoint_strip {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(291/1000:ℝ)
  · by_cases h1 : a≤(479/2500:ℝ)
    · by_cases h2 : a≤(423/2500:ℝ)
      · by_cases h3 : a≤(399/2500:ℝ)
        · by_cases h4 : a≤(383/2500:ℝ)
          · exact coverage000 ⟨ha.1,h4⟩ hz
          · by_cases h5 : a≤(391/2500:ℝ)
            · exact coverage001 ⟨(le_of_lt (lt_of_not_ge h4)),h5⟩ hz
            · exact coverage002 ⟨(le_of_lt (lt_of_not_ge h5)),h3⟩ hz
        · by_cases h6 : a≤(407/2500:ℝ)
          · exact coverage003 ⟨(le_of_lt (lt_of_not_ge h3)),h6⟩ hz
          · by_cases h7 : a≤(83/500:ℝ)
            · exact coverage004 ⟨(le_of_lt (lt_of_not_ge h6)),h7⟩ hz
            · exact coverage005 ⟨(le_of_lt (lt_of_not_ge h7)),h2⟩ hz
      · by_cases h8 : a≤(447/2500:ℝ)
        · by_cases h9 : a≤(431/2500:ℝ)
          · exact coverage006 ⟨(le_of_lt (lt_of_not_ge h2)),h9⟩ hz
          · by_cases h10 : a≤(439/2500:ℝ)
            · exact coverage007 ⟨(le_of_lt (lt_of_not_ge h9)),h10⟩ hz
            · exact coverage008 ⟨(le_of_lt (lt_of_not_ge h10)),h8⟩ hz
        · by_cases h11 : a≤(463/2500:ℝ)
          · by_cases h12 : a≤(91/500:ℝ)
            · exact coverage009 ⟨(le_of_lt (lt_of_not_ge h8)),h12⟩ hz
            · exact coverage010 ⟨(le_of_lt (lt_of_not_ge h12)),h11⟩ hz
          · by_cases h13 : a≤(471/2500:ℝ)
            · exact coverage011 ⟨(le_of_lt (lt_of_not_ge h11)),h13⟩ hz
            · exact coverage012 ⟨(le_of_lt (lt_of_not_ge h13)),h1⟩ hz
    · by_cases h14 : a≤(47/200:ℝ)
      · by_cases h15 : a≤(203/1000:ℝ)
        · by_cases h16 : a≤(487/2500:ℝ)
          · exact coverage013 ⟨(le_of_lt (lt_of_not_ge h1)),h16⟩ hz
          · by_cases h17 : a≤(99/500:ℝ)
            · exact coverage014 ⟨(le_of_lt (lt_of_not_ge h16)),h17⟩ hz
            · exact coverage015 ⟨(le_of_lt (lt_of_not_ge h17)),h15⟩ hz
        · by_cases h18 : a≤(219/1000:ℝ)
          · by_cases h19 : a≤(211/1000:ℝ)
            · exact coverage016 ⟨(le_of_lt (lt_of_not_ge h15)),h19⟩ hz
            · exact coverage017 ⟨(le_of_lt (lt_of_not_ge h19)),h18⟩ hz
          · by_cases h20 : a≤(227/1000:ℝ)
            · exact coverage018 ⟨(le_of_lt (lt_of_not_ge h18)),h20⟩ hz
            · exact coverage019 ⟨(le_of_lt (lt_of_not_ge h20)),h14⟩ hz
      · by_cases h21 : a≤(259/1000:ℝ)
        · by_cases h22 : a≤(243/1000:ℝ)
          · exact coverage020 ⟨(le_of_lt (lt_of_not_ge h14)),h22⟩ hz
          · by_cases h23 : a≤(251/1000:ℝ)
            · exact coverage021 ⟨(le_of_lt (lt_of_not_ge h22)),h23⟩ hz
            · exact coverage022 ⟨(le_of_lt (lt_of_not_ge h23)),h21⟩ hz
        · by_cases h24 : a≤(11/40:ℝ)
          · by_cases h25 : a≤(267/1000:ℝ)
            · exact coverage023 ⟨(le_of_lt (lt_of_not_ge h21)),h25⟩ hz
            · exact coverage024 ⟨(le_of_lt (lt_of_not_ge h25)),h24⟩ hz
          · by_cases h26 : a≤(283/1000:ℝ)
            · exact coverage025 ⟨(le_of_lt (lt_of_not_ge h24)),h26⟩ hz
            · exact coverage026 ⟨(le_of_lt (lt_of_not_ge h26)),h0⟩ hz
  · by_cases h27 : a≤(49/100:ℝ)
    · by_cases h28 : a≤(189/500:ℝ)
      · by_cases h29 : a≤(33/100:ℝ)
        · by_cases h30 : a≤(299/1000:ℝ)
          · exact coverage027 ⟨(le_of_lt (lt_of_not_ge h0)),h30⟩ hz
          · by_cases h31 : a≤(157/500:ℝ)
            · exact coverage028 ⟨(le_of_lt (lt_of_not_ge h30)),h31⟩ hz
            · exact coverage029 ⟨(le_of_lt (lt_of_not_ge h31)),h29⟩ hz
        · by_cases h32 : a≤(173/500:ℝ)
          · exact coverage030 ⟨(le_of_lt (lt_of_not_ge h29)),h32⟩ hz
          · by_cases h33 : a≤(181/500:ℝ)
            · exact coverage031 ⟨(le_of_lt (lt_of_not_ge h32)),h33⟩ hz
            · exact coverage032 ⟨(le_of_lt (lt_of_not_ge h33)),h28⟩ hz
      · by_cases h34 : a≤(213/500:ℝ)
        · by_cases h35 : a≤(197/500:ℝ)
          · exact coverage033 ⟨(le_of_lt (lt_of_not_ge h28)),h35⟩ hz
          · by_cases h36 : a≤(41/100:ℝ)
            · exact coverage034 ⟨(le_of_lt (lt_of_not_ge h35)),h36⟩ hz
            · exact coverage035 ⟨(le_of_lt (lt_of_not_ge h36)),h34⟩ hz
        · by_cases h37 : a≤(229/500:ℝ)
          · by_cases h38 : a≤(221/500:ℝ)
            · exact coverage036 ⟨(le_of_lt (lt_of_not_ge h34)),h38⟩ hz
            · exact coverage037 ⟨(le_of_lt (lt_of_not_ge h38)),h37⟩ hz
          · by_cases h39 : a≤(237/500:ℝ)
            · exact coverage038 ⟨(le_of_lt (lt_of_not_ge h37)),h39⟩ hz
            · exact coverage039 ⟨(le_of_lt (lt_of_not_ge h39)),h27⟩ hz
    · by_cases h40 : a≤(88/125:ℝ)
      · by_cases h41 : a≤(72/125:ℝ)
        · by_cases h42 : a≤(64/125:ℝ)
          · exact coverage040 ⟨(le_of_lt (lt_of_not_ge h27)),h42⟩ hz
          · by_cases h43 : a≤(68/125:ℝ)
            · exact coverage041 ⟨(le_of_lt (lt_of_not_ge h42)),h43⟩ hz
            · exact coverage042 ⟨(le_of_lt (lt_of_not_ge h43)),h41⟩ hz
        · by_cases h44 : a≤(16/25:ℝ)
          · by_cases h45 : a≤(76/125:ℝ)
            · exact coverage043 ⟨(le_of_lt (lt_of_not_ge h41)),h45⟩ hz
            · exact coverage044 ⟨(le_of_lt (lt_of_not_ge h45)),h44⟩ hz
          · by_cases h46 : a≤(84/125:ℝ)
            · exact coverage045 ⟨(le_of_lt (lt_of_not_ge h44)),h46⟩ hz
            · exact coverage046 ⟨(le_of_lt (lt_of_not_ge h46)),h40⟩ hz
      · by_cases h47 : a≤(4/5:ℝ)
        · by_cases h48 : a≤(92/125:ℝ)
          · exact coverage047 ⟨(le_of_lt (lt_of_not_ge h40)),h48⟩ hz
          · by_cases h49 : a≤(96/125:ℝ)
            · exact coverage048 ⟨(le_of_lt (lt_of_not_ge h48)),h49⟩ hz
            · exact coverage049 ⟨(le_of_lt (lt_of_not_ge h49)),h47⟩ hz
        · by_cases h50 : a≤(477/500:ℝ)
          · by_cases h51 : a≤(22/25:ℝ)
            · exact coverage050 ⟨(le_of_lt (lt_of_not_ge h47)),h51⟩ hz
            · exact coverage051 ⟨(le_of_lt (lt_of_not_ge h51)),h50⟩ hz
          · by_cases h52 : a≤(493/500:ℝ)
            · exact coverage052 ⟨(le_of_lt (lt_of_not_ge h50)),h52⟩ hz
            · exact coverage053 ⟨(le_of_lt (lt_of_not_ge h52)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

end


