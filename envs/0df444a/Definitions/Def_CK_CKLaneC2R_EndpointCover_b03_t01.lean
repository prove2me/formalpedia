-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b03_t01
-- name    : CK_CKLaneC2R_EndpointCover_b03_t01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:08:38.995281+00:00
-- url     : https://prove2.me/theorems/b6b7d2f4-696b-41bd-942a-5626bf83208a
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 2 of 6 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 2 of 6 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 2 of 6 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 2 of 6 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 2 of 6 of 3).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B018
import Definitions.Def_CK_CKLaneC2R_EpCells_B019
import Definitions.Def_CK_CKLaneC2R_EpCells_B020
namespace CKLaneC2R.EndpointCover

theorem cover_sub_015 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : ¬ (a ≤ ((5649/32000 : ℚ) : ℝ))) (h1613 : ¬ (a ≤ ((12147/64000 : ℚ) : ℝ))) (h1869 : ¬ (a ≤ ((25143/128000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1997 : a ≤ ((10227/51200 : ℚ) : ℝ)
  · -- left
    by_cases h1998 : a ≤ ((101421/512000 : ℚ) : ℝ)
    · -- left
      by_cases h1999 : a ≤ ((201993/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h2000 : a ≤ ((403137/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2001 : a ≤ ((32217/163840 : ℚ) : ℝ)
          · -- left
            by_cases h2002 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2003 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1085_pos (not_le.mp h1869).le h2001 hz1 h2003 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1087_pos (not_le.mp h1869).le h2001 (not_le.mp h2003).le h2002 hz
            · -- right
              by_cases h2004 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1093_pos (not_le.mp h1869).le h2001 (not_le.mp h2002).le h2004 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1095_pos (not_le.mp h1869).le h2001 (not_le.mp h2004).le hz2 hz
          · -- right
            by_cases h2005 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2006 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1086_pos (not_le.mp h2001).le h2000 hz1 h2006 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1088_pos (not_le.mp h2001).le h2000 (not_le.mp h2006).le h2005 hz
            · -- right
              by_cases h2007 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1094_pos (not_le.mp h2001).le h2000 (not_le.mp h2005).le h2007 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1096_pos (not_le.mp h2001).le h2000 (not_le.mp h2007).le hz2 hz
        · -- right
          by_cases h2008 : a ≤ ((807123/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2009 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2010 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1089_pos (not_le.mp h2000).le h2008 hz1 h2010 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1091_pos (not_le.mp h2000).le h2008 (not_le.mp h2010).le h2009 hz
            · -- right
              by_cases h2011 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1097_pos (not_le.mp h2000).le h2008 (not_le.mp h2009).le h2011 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1099_pos (not_le.mp h2000).le h2008 (not_le.mp h2011).le hz2 hz
          · -- right
            by_cases h2012 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2013 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1090_pos (not_le.mp h2008).le h1999 hz1 h2013 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1092_pos (not_le.mp h2008).le h1999 (not_le.mp h2013).le h2012 hz
            · -- right
              by_cases h2014 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1098_pos (not_le.mp h2008).le h1999 (not_le.mp h2012).le h2014 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1100_pos (not_le.mp h2008).le h1999 (not_le.mp h2014).le hz2 hz
      · -- right
        by_cases h2015 : a ≤ ((80967/409600 : ℚ) : ℝ)
        · -- left
          by_cases h2016 : a ≤ ((808821/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2017 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2018 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1101_pos (not_le.mp h1999).le h2016 hz1 h2018 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1103_pos (not_le.mp h1999).le h2016 (not_le.mp h2018).le h2017 hz
            · -- right
              by_cases h2019 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1109_pos (not_le.mp h1999).le h2016 (not_le.mp h2017).le h2019 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1111_pos (not_le.mp h1999).le h2016 (not_le.mp h2019).le hz2 hz
          · -- right
            by_cases h2020 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2021 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1102_pos (not_le.mp h2016).le h2015 hz1 h2021 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1104_pos (not_le.mp h2016).le h2015 (not_le.mp h2021).le h2020 hz
            · -- right
              by_cases h2022 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1110_pos (not_le.mp h2016).le h2015 (not_le.mp h2020).le h2022 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1112_pos (not_le.mp h2016).le h2015 (not_le.mp h2022).le hz2 hz
        · -- right
          by_cases h2023 : a ≤ ((810519/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2024 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2025 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1105_pos (not_le.mp h2015).le h2023 hz1 h2025 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1107_pos (not_le.mp h2015).le h2023 (not_le.mp h2025).le h2024 hz
            · -- right
              by_cases h2026 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1113_pos (not_le.mp h2015).le h2023 (not_le.mp h2024).le h2026 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1115_pos (not_le.mp h2015).le h2023 (not_le.mp h2026).le hz2 hz
          · -- right
            by_cases h2027 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2028 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1106_pos (not_le.mp h2023).le h1998 hz1 h2028 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1108_pos (not_le.mp h2023).le h1998 (not_le.mp h2028).le h2027 hz
            · -- right
              by_cases h2029 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1114_pos (not_le.mp h2023).le h1998 (not_le.mp h2027).le h2029 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1116_pos (not_le.mp h2023).le h1998 (not_le.mp h2029).le hz2 hz
    · -- right
      by_cases h2030 : a ≤ ((203691/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h2031 : a ≤ ((406533/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2032 : a ≤ ((812217/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2033 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2034 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1117_pos (not_le.mp h1998).le h2032 hz1 h2034 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1119_pos (not_le.mp h1998).le h2032 (not_le.mp h2034).le h2033 hz
            · -- right
              by_cases h2035 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1125_pos (not_le.mp h1998).le h2032 (not_le.mp h2033).le h2035 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1127_pos (not_le.mp h1998).le h2032 (not_le.mp h2035).le hz2 hz
          · -- right
            by_cases h2036 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2037 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1118_pos (not_le.mp h2032).le h2031 hz1 h2037 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1120_pos (not_le.mp h2032).le h2031 (not_le.mp h2037).le h2036 hz
            · -- right
              by_cases h2038 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1126_pos (not_le.mp h2032).le h2031 (not_le.mp h2036).le h2038 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1128_pos (not_le.mp h2032).le h2031 (not_le.mp h2038).le hz2 hz
        · -- right
          by_cases h2039 : a ≤ ((162783/819200 : ℚ) : ℝ)
          · -- left
            by_cases h2040 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2041 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1121_pos (not_le.mp h2031).le h2039 hz1 h2041 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1123_pos (not_le.mp h2031).le h2039 (not_le.mp h2041).le h2040 hz
            · -- right
              by_cases h2042 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1129_pos (not_le.mp h2031).le h2039 (not_le.mp h2040).le h2042 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1131_pos (not_le.mp h2031).le h2039 (not_le.mp h2042).le hz2 hz
          · -- right
            by_cases h2043 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2044 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1122_pos (not_le.mp h2039).le h2030 hz1 h2044 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1124_pos (not_le.mp h2039).le h2030 (not_le.mp h2044).le h2043 hz
            · -- right
              by_cases h2045 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1130_pos (not_le.mp h2039).le h2030 (not_le.mp h2043).le h2045 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1132_pos (not_le.mp h2039).le h2030 (not_le.mp h2045).le hz2 hz
      · -- right
        by_cases h2046 : a ≤ ((408231/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2047 : a ≤ ((815613/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2048 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2049 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1133_pos (not_le.mp h2030).le h2047 hz1 h2049 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1135_pos (not_le.mp h2030).le h2047 (not_le.mp h2049).le h2048 hz
            · -- right
              by_cases h2050 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1141_pos (not_le.mp h2030).le h2047 (not_le.mp h2048).le h2050 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1143_pos (not_le.mp h2030).le h2047 (not_le.mp h2050).le hz2 hz
          · -- right
            by_cases h2051 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2052 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1134_pos (not_le.mp h2047).le h2046 hz1 h2052 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1136_pos (not_le.mp h2047).le h2046 (not_le.mp h2052).le h2051 hz
            · -- right
              by_cases h2053 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1142_pos (not_le.mp h2047).le h2046 (not_le.mp h2051).le h2053 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1144_pos (not_le.mp h2047).le h2046 (not_le.mp h2053).le hz2 hz
        · -- right
          by_cases h2054 : a ≤ ((817311/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2055 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2056 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1137_pos (not_le.mp h2046).le h2054 hz1 h2056 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1139_pos (not_le.mp h2046).le h2054 (not_le.mp h2056).le h2055 hz
            · -- right
              by_cases h2057 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1145_pos (not_le.mp h2046).le h2054 (not_le.mp h2055).le h2057 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1147_pos (not_le.mp h2046).le h2054 (not_le.mp h2057).le hz2 hz
          · -- right
            by_cases h2058 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2059 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1138_pos (not_le.mp h2054).le h1997 hz1 h2059 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1140_pos (not_le.mp h2054).le h1997 (not_le.mp h2059).le h2058 hz
            · -- right
              by_cases h2060 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1146_pos (not_le.mp h2054).le h1997 (not_le.mp h2058).le h2060 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1148_pos (not_le.mp h2054).le h1997 (not_le.mp h2060).le hz2 hz
  · -- right
    by_cases h2061 : a ≤ ((103119/512000 : ℚ) : ℝ)
    · -- left
      by_cases h2062 : a ≤ ((205389/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h2063 : a ≤ ((409929/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2064 : a ≤ ((819009/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2065 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2066 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1149_pos (not_le.mp h1997).le h2064 hz1 h2066 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1151_pos (not_le.mp h1997).le h2064 (not_le.mp h2066).le h2065 hz
            · -- right
              by_cases h2067 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1157_pos (not_le.mp h1997).le h2064 (not_le.mp h2065).le h2067 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1159_pos (not_le.mp h1997).le h2064 (not_le.mp h2067).le hz2 hz
          · -- right
            by_cases h2068 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2069 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1150_pos (not_le.mp h2064).le h2063 hz1 h2069 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1152_pos (not_le.mp h2064).le h2063 (not_le.mp h2069).le h2068 hz
            · -- right
              by_cases h2070 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1158_pos (not_le.mp h2064).le h2063 (not_le.mp h2068).le h2070 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1160_pos (not_le.mp h2064).le h2063 (not_le.mp h2070).le hz2 hz
        · -- right
          by_cases h2071 : a ≤ ((820707/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2072 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2073 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1153_pos (not_le.mp h2063).le h2071 hz1 h2073 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1155_pos (not_le.mp h2063).le h2071 (not_le.mp h2073).le h2072 hz
            · -- right
              by_cases h2074 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1161_pos (not_le.mp h2063).le h2071 (not_le.mp h2072).le h2074 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1163_pos (not_le.mp h2063).le h2071 (not_le.mp h2074).le hz2 hz
          · -- right
            by_cases h2075 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2076 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1154_pos (not_le.mp h2071).le h2062 hz1 h2076 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1156_pos (not_le.mp h2071).le h2062 (not_le.mp h2076).le h2075 hz
            · -- right
              by_cases h2077 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1162_pos (not_le.mp h2071).le h2062 (not_le.mp h2075).le h2077 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1164_pos (not_le.mp h2071).le h2062 (not_le.mp h2077).le hz2 hz
      · -- right
        by_cases h2078 : a ≤ ((411627/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2079 : a ≤ ((164481/819200 : ℚ) : ℝ)
          · -- left
            by_cases h2080 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2081 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1165_pos (not_le.mp h2062).le h2079 hz1 h2081 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1167_pos (not_le.mp h2062).le h2079 (not_le.mp h2081).le h2080 hz
            · -- right
              by_cases h2082 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1173_pos (not_le.mp h2062).le h2079 (not_le.mp h2080).le h2082 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1175_pos (not_le.mp h2062).le h2079 (not_le.mp h2082).le hz2 hz
          · -- right
            by_cases h2083 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2084 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1166_pos (not_le.mp h2079).le h2078 hz1 h2084 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1168_pos (not_le.mp h2079).le h2078 (not_le.mp h2084).le h2083 hz
            · -- right
              by_cases h2085 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1174_pos (not_le.mp h2079).le h2078 (not_le.mp h2083).le h2085 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1176_pos (not_le.mp h2079).le h2078 (not_le.mp h2085).le hz2 hz
        · -- right
          by_cases h2086 : a ≤ ((824103/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2087 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2088 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1169_pos (not_le.mp h2078).le h2086 hz1 h2088 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1171_pos (not_le.mp h2078).le h2086 (not_le.mp h2088).le h2087 hz
            · -- right
              by_cases h2089 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1177_pos (not_le.mp h2078).le h2086 (not_le.mp h2087).le h2089 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1179_pos (not_le.mp h2078).le h2086 (not_le.mp h2089).le hz2 hz
          · -- right
            by_cases h2090 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2091 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1170_pos (not_le.mp h2086).le h2061 hz1 h2091 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1172_pos (not_le.mp h2086).le h2061 (not_le.mp h2091).le h2090 hz
            · -- right
              by_cases h2092 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1178_pos (not_le.mp h2086).le h2061 (not_le.mp h2090).le h2092 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1180_pos (not_le.mp h2086).le h2061 (not_le.mp h2092).le hz2 hz
    · -- right
      by_cases h2093 : a ≤ ((207087/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h2094 : a ≤ ((16533/81920 : ℚ) : ℝ)
        · -- left
          by_cases h2095 : a ≤ ((825801/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2096 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2097 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1181_pos (not_le.mp h2061).le h2095 hz1 h2097 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1183_pos (not_le.mp h2061).le h2095 (not_le.mp h2097).le h2096 hz
            · -- right
              by_cases h2098 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1189_pos (not_le.mp h2061).le h2095 (not_le.mp h2096).le h2098 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1191_pos (not_le.mp h2061).le h2095 (not_le.mp h2098).le hz2 hz
          · -- right
            by_cases h2099 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2100 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1182_pos (not_le.mp h2095).le h2094 hz1 h2100 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1184_pos (not_le.mp h2095).le h2094 (not_le.mp h2100).le h2099 hz
            · -- right
              by_cases h2101 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1190_pos (not_le.mp h2095).le h2094 (not_le.mp h2099).le h2101 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1192_pos (not_le.mp h2095).le h2094 (not_le.mp h2101).le hz2 hz
        · -- right
          by_cases h2102 : a ≤ ((827499/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2103 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2104 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1185_pos (not_le.mp h2094).le h2102 hz1 h2104 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1187_pos (not_le.mp h2094).le h2102 (not_le.mp h2104).le h2103 hz
            · -- right
              by_cases h2105 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1193_pos (not_le.mp h2094).le h2102 (not_le.mp h2103).le h2105 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1195_pos (not_le.mp h2094).le h2102 (not_le.mp h2105).le hz2 hz
          · -- right
            by_cases h2106 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2107 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1186_pos (not_le.mp h2102).le h2093 hz1 h2107 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1188_pos (not_le.mp h2102).le h2093 (not_le.mp h2107).le h2106 hz
            · -- right
              by_cases h2108 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1194_pos (not_le.mp h2102).le h2093 (not_le.mp h2106).le h2108 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1196_pos (not_le.mp h2102).le h2093 (not_le.mp h2108).le hz2 hz
      · -- right
        by_cases h2109 : a ≤ ((415023/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2110 : a ≤ ((829197/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2111 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2112 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1197_pos (not_le.mp h2093).le h2110 hz1 h2112 hz
              · -- right
                exact CKLaneC2R.EpCells.B019.e1199_pos (not_le.mp h2093).le h2110 (not_le.mp h2112).le h2111 hz
            · -- right
              by_cases h2113 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1205_pos (not_le.mp h2093).le h2110 (not_le.mp h2111).le h2113 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1207_pos (not_le.mp h2093).le h2110 (not_le.mp h2113).le hz2 hz
          · -- right
            by_cases h2114 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2115 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B019.e1198_pos (not_le.mp h2110).le h2109 hz1 h2115 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1200_pos (not_le.mp h2110).le h2109 (not_le.mp h2115).le h2114 hz
            · -- right
              by_cases h2116 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1206_pos (not_le.mp h2110).le h2109 (not_le.mp h2114).le h2116 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1208_pos (not_le.mp h2110).le h2109 (not_le.mp h2116).le hz2 hz
        · -- right
          by_cases h2117 : a ≤ ((166179/819200 : ℚ) : ℝ)
          · -- left
            by_cases h2118 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2119 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1201_pos (not_le.mp h2109).le h2117 hz1 h2119 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1203_pos (not_le.mp h2109).le h2117 (not_le.mp h2119).le h2118 hz
            · -- right
              by_cases h2120 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1209_pos (not_le.mp h2109).le h2117 (not_le.mp h2118).le h2120 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1211_pos (not_le.mp h2109).le h2117 (not_le.mp h2120).le hz2 hz
          · -- right
            by_cases h2121 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2122 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1202_pos (not_le.mp h2117).le h3 hz1 h2122 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1204_pos (not_le.mp h2117).le h3 (not_le.mp h2122).le h2121 hz
            · -- right
              by_cases h2123 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1210_pos (not_le.mp h2117).le h3 (not_le.mp h2121).le h2123 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1212_pos (not_le.mp h2117).le h3 (not_le.mp h2123).le hz2 hz

end CKLaneC2R.EndpointCover


