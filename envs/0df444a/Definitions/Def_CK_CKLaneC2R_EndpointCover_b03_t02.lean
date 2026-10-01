-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b03_t02
-- name    : CK_CKLaneC2R_EndpointCover_b03_t02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:56:26.277468+00:00
-- url     : https://prove2.me/theorems/376e0a84-64c7-4381-916d-2478e966a6b9
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 3 of 6 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 3 of 6 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 3 of 6 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 3 of 6 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 3 of 6 of 3).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B020
import Definitions.Def_CK_CKLaneC2R_EpCells_B021
import Definitions.Def_CK_CKLaneC2R_EpCells_B022
namespace CKLaneC2R.EndpointCover

theorem cover_sub_016 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((3249/16000 : ℚ) : ℝ))) (h2124 : a ≤ ((7347/32000 : ℚ) : ℝ)) (h2125 : a ≤ ((2769/12800 : ℚ) : ℝ)) (h2126 : a ≤ ((26841/128000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h2127 : a ≤ ((52833/256000 : ℚ) : ℝ)
  · -- left
    by_cases h2128 : a ≤ ((104817/512000 : ℚ) : ℝ)
    · -- left
      by_cases h2129 : a ≤ ((41757/204800 : ℚ) : ℝ)
      · -- left
        by_cases h2130 : a ≤ ((416721/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2131 : a ≤ ((832593/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2132 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2133 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1213_pos (not_le.mp h3).le h2131 hz1 h2133 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1215_pos (not_le.mp h3).le h2131 (not_le.mp h2133).le h2132 hz
            · -- right
              by_cases h2134 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1221_pos (not_le.mp h3).le h2131 (not_le.mp h2132).le h2134 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1223_pos (not_le.mp h3).le h2131 (not_le.mp h2134).le hz2 hz
          · -- right
            by_cases h2135 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2136 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1214_pos (not_le.mp h2131).le h2130 hz1 h2136 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1216_pos (not_le.mp h2131).le h2130 (not_le.mp h2136).le h2135 hz
            · -- right
              by_cases h2137 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1222_pos (not_le.mp h2131).le h2130 (not_le.mp h2135).le h2137 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1224_pos (not_le.mp h2131).le h2130 (not_le.mp h2137).le hz2 hz
        · -- right
          by_cases h2138 : a ≤ ((834291/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2139 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2140 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1217_pos (not_le.mp h2130).le h2138 hz1 h2140 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1219_pos (not_le.mp h2130).le h2138 (not_le.mp h2140).le h2139 hz
            · -- right
              by_cases h2141 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1225_pos (not_le.mp h2130).le h2138 (not_le.mp h2139).le h2141 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1227_pos (not_le.mp h2130).le h2138 (not_le.mp h2141).le hz2 hz
          · -- right
            by_cases h2142 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2143 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1218_pos (not_le.mp h2138).le h2129 hz1 h2143 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1220_pos (not_le.mp h2138).le h2129 (not_le.mp h2143).le h2142 hz
            · -- right
              by_cases h2144 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1226_pos (not_le.mp h2138).le h2129 (not_le.mp h2142).le h2144 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1228_pos (not_le.mp h2138).le h2129 (not_le.mp h2144).le hz2 hz
      · -- right
        by_cases h2145 : a ≤ ((418419/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2146 : a ≤ ((835989/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2147 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2148 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1229_pos (not_le.mp h2129).le h2146 hz1 h2148 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1231_pos (not_le.mp h2129).le h2146 (not_le.mp h2148).le h2147 hz
            · -- right
              by_cases h2149 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1237_pos (not_le.mp h2129).le h2146 (not_le.mp h2147).le h2149 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1239_pos (not_le.mp h2129).le h2146 (not_le.mp h2149).le hz2 hz
          · -- right
            by_cases h2150 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2151 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1230_pos (not_le.mp h2146).le h2145 hz1 h2151 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1232_pos (not_le.mp h2146).le h2145 (not_le.mp h2151).le h2150 hz
            · -- right
              by_cases h2152 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1238_pos (not_le.mp h2146).le h2145 (not_le.mp h2150).le h2152 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1240_pos (not_le.mp h2146).le h2145 (not_le.mp h2152).le hz2 hz
        · -- right
          by_cases h2153 : a ≤ ((837687/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2154 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2155 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1233_pos (not_le.mp h2145).le h2153 hz1 h2155 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1235_pos (not_le.mp h2145).le h2153 (not_le.mp h2155).le h2154 hz
            · -- right
              by_cases h2156 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1241_pos (not_le.mp h2145).le h2153 (not_le.mp h2154).le h2156 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1243_pos (not_le.mp h2145).le h2153 (not_le.mp h2156).le hz2 hz
          · -- right
            by_cases h2157 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2158 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1234_pos (not_le.mp h2153).le h2128 hz1 h2158 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1236_pos (not_le.mp h2153).le h2128 (not_le.mp h2158).le h2157 hz
            · -- right
              by_cases h2159 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1242_pos (not_le.mp h2153).le h2128 (not_le.mp h2157).le h2159 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1244_pos (not_le.mp h2153).le h2128 (not_le.mp h2159).le hz2 hz
    · -- right
      by_cases h2160 : a ≤ ((210483/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h2161 : a ≤ ((420117/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2162 : a ≤ ((167877/819200 : ℚ) : ℝ)
          · -- left
            by_cases h2163 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2164 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1245_pos (not_le.mp h2128).le h2162 hz1 h2164 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1247_pos (not_le.mp h2128).le h2162 (not_le.mp h2164).le h2163 hz
            · -- right
              by_cases h2165 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1253_pos (not_le.mp h2128).le h2162 (not_le.mp h2163).le h2165 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1255_pos (not_le.mp h2128).le h2162 (not_le.mp h2165).le hz2 hz
          · -- right
            by_cases h2166 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2167 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1246_pos (not_le.mp h2162).le h2161 hz1 h2167 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1248_pos (not_le.mp h2162).le h2161 (not_le.mp h2167).le h2166 hz
            · -- right
              by_cases h2168 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1254_pos (not_le.mp h2162).le h2161 (not_le.mp h2166).le h2168 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1256_pos (not_le.mp h2162).le h2161 (not_le.mp h2168).le hz2 hz
        · -- right
          by_cases h2169 : a ≤ ((841083/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2170 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2171 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1249_pos (not_le.mp h2161).le h2169 hz1 h2171 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1251_pos (not_le.mp h2161).le h2169 (not_le.mp h2171).le h2170 hz
            · -- right
              by_cases h2172 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1257_pos (not_le.mp h2161).le h2169 (not_le.mp h2170).le h2172 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1259_pos (not_le.mp h2161).le h2169 (not_le.mp h2172).le hz2 hz
          · -- right
            by_cases h2173 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2174 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1250_pos (not_le.mp h2169).le h2160 hz1 h2174 hz
              · -- right
                exact CKLaneC2R.EpCells.B020.e1252_pos (not_le.mp h2169).le h2160 (not_le.mp h2174).le h2173 hz
            · -- right
              by_cases h2175 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B020.e1258_pos (not_le.mp h2169).le h2160 (not_le.mp h2173).le h2175 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1260_pos (not_le.mp h2169).le h2160 (not_le.mp h2175).le hz2 hz
      · -- right
        by_cases h2176 : a ≤ ((84363/409600 : ℚ) : ℝ)
        · -- left
          by_cases h2177 : a ≤ ((842781/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2178 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2179 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1261_pos (not_le.mp h2160).le h2177 hz1 h2179 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1263_pos (not_le.mp h2160).le h2177 (not_le.mp h2179).le h2178 hz
            · -- right
              by_cases h2180 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1269_pos (not_le.mp h2160).le h2177 (not_le.mp h2178).le h2180 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1271_pos (not_le.mp h2160).le h2177 (not_le.mp h2180).le hz2 hz
          · -- right
            by_cases h2181 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2182 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1262_pos (not_le.mp h2177).le h2176 hz1 h2182 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1264_pos (not_le.mp h2177).le h2176 (not_le.mp h2182).le h2181 hz
            · -- right
              by_cases h2183 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1270_pos (not_le.mp h2177).le h2176 (not_le.mp h2181).le h2183 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1272_pos (not_le.mp h2177).le h2176 (not_le.mp h2183).le hz2 hz
        · -- right
          by_cases h2184 : a ≤ ((844479/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2185 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2186 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1265_pos (not_le.mp h2176).le h2184 hz1 h2186 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1267_pos (not_le.mp h2176).le h2184 (not_le.mp h2186).le h2185 hz
            · -- right
              by_cases h2187 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1273_pos (not_le.mp h2176).le h2184 (not_le.mp h2185).le h2187 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1275_pos (not_le.mp h2176).le h2184 (not_le.mp h2187).le hz2 hz
          · -- right
            by_cases h2188 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2189 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1266_pos (not_le.mp h2184).le h2127 hz1 h2189 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1268_pos (not_le.mp h2184).le h2127 (not_le.mp h2189).le h2188 hz
            · -- right
              by_cases h2190 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1274_pos (not_le.mp h2184).le h2127 (not_le.mp h2188).le h2190 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1276_pos (not_le.mp h2184).le h2127 (not_le.mp h2190).le hz2 hz
  · -- right
    by_cases h2191 : a ≤ ((21303/102400 : ℚ) : ℝ)
    · -- left
      by_cases h2192 : a ≤ ((212181/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h2193 : a ≤ ((423513/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2194 : a ≤ ((846177/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2195 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2196 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1277_pos (not_le.mp h2127).le h2194 hz1 h2196 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1279_pos (not_le.mp h2127).le h2194 (not_le.mp h2196).le h2195 hz
            · -- right
              by_cases h2197 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1285_pos (not_le.mp h2127).le h2194 (not_le.mp h2195).le h2197 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1287_pos (not_le.mp h2127).le h2194 (not_le.mp h2197).le hz2 hz
          · -- right
            by_cases h2198 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2199 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1278_pos (not_le.mp h2194).le h2193 hz1 h2199 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1280_pos (not_le.mp h2194).le h2193 (not_le.mp h2199).le h2198 hz
            · -- right
              by_cases h2200 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1286_pos (not_le.mp h2194).le h2193 (not_le.mp h2198).le h2200 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1288_pos (not_le.mp h2194).le h2193 (not_le.mp h2200).le hz2 hz
        · -- right
          by_cases h2201 : a ≤ ((6783/32768 : ℚ) : ℝ)
          · -- left
            by_cases h2202 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2203 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1281_pos (not_le.mp h2193).le h2201 hz1 h2203 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1283_pos (not_le.mp h2193).le h2201 (not_le.mp h2203).le h2202 hz
            · -- right
              by_cases h2204 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1289_pos (not_le.mp h2193).le h2201 (not_le.mp h2202).le h2204 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1291_pos (not_le.mp h2193).le h2201 (not_le.mp h2204).le hz2 hz
          · -- right
            by_cases h2205 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2206 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1282_pos (not_le.mp h2201).le h2192 hz1 h2206 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1284_pos (not_le.mp h2201).le h2192 (not_le.mp h2206).le h2205 hz
            · -- right
              by_cases h2207 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1290_pos (not_le.mp h2201).le h2192 (not_le.mp h2205).le h2207 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1292_pos (not_le.mp h2201).le h2192 (not_le.mp h2207).le hz2 hz
      · -- right
        by_cases h2208 : a ≤ ((425211/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2209 : a ≤ ((849573/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2210 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2211 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1293_pos (not_le.mp h2192).le h2209 hz1 h2211 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1295_pos (not_le.mp h2192).le h2209 (not_le.mp h2211).le h2210 hz
            · -- right
              by_cases h2212 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1301_pos (not_le.mp h2192).le h2209 (not_le.mp h2210).le h2212 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1303_pos (not_le.mp h2192).le h2209 (not_le.mp h2212).le hz2 hz
          · -- right
            by_cases h2213 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2214 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1294_pos (not_le.mp h2209).le h2208 hz1 h2214 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1296_pos (not_le.mp h2209).le h2208 (not_le.mp h2214).le h2213 hz
            · -- right
              by_cases h2215 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1302_pos (not_le.mp h2209).le h2208 (not_le.mp h2213).le h2215 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1304_pos (not_le.mp h2209).le h2208 (not_le.mp h2215).le hz2 hz
        · -- right
          by_cases h2216 : a ≤ ((851271/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2217 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2218 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1297_pos (not_le.mp h2208).le h2216 hz1 h2218 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1299_pos (not_le.mp h2208).le h2216 (not_le.mp h2218).le h2217 hz
            · -- right
              by_cases h2219 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1305_pos (not_le.mp h2208).le h2216 (not_le.mp h2217).le h2219 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1307_pos (not_le.mp h2208).le h2216 (not_le.mp h2219).le hz2 hz
          · -- right
            by_cases h2220 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2221 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1298_pos (not_le.mp h2216).le h2191 hz1 h2221 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1300_pos (not_le.mp h2216).le h2191 (not_le.mp h2221).le h2220 hz
            · -- right
              by_cases h2222 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1306_pos (not_le.mp h2216).le h2191 (not_le.mp h2220).le h2222 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1308_pos (not_le.mp h2216).le h2191 (not_le.mp h2222).le hz2 hz
    · -- right
      by_cases h2223 : a ≤ ((213879/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h2224 : a ≤ ((426909/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2225 : a ≤ ((852969/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2226 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2227 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1309_pos (not_le.mp h2191).le h2225 hz1 h2227 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1311_pos (not_le.mp h2191).le h2225 (not_le.mp h2227).le h2226 hz
            · -- right
              by_cases h2228 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1317_pos (not_le.mp h2191).le h2225 (not_le.mp h2226).le h2228 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1319_pos (not_le.mp h2191).le h2225 (not_le.mp h2228).le hz2 hz
          · -- right
            by_cases h2229 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2230 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1310_pos (not_le.mp h2225).le h2224 hz1 h2230 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1312_pos (not_le.mp h2225).le h2224 (not_le.mp h2230).le h2229 hz
            · -- right
              by_cases h2231 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1318_pos (not_le.mp h2225).le h2224 (not_le.mp h2229).le h2231 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1320_pos (not_le.mp h2225).le h2224 (not_le.mp h2231).le hz2 hz
        · -- right
          by_cases h2232 : a ≤ ((854667/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2233 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2234 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1313_pos (not_le.mp h2224).le h2232 hz1 h2234 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1315_pos (not_le.mp h2224).le h2232 (not_le.mp h2234).le h2233 hz
            · -- right
              by_cases h2235 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1321_pos (not_le.mp h2224).le h2232 (not_le.mp h2233).le h2235 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1323_pos (not_le.mp h2224).le h2232 (not_le.mp h2235).le hz2 hz
          · -- right
            by_cases h2236 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2237 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B021.e1314_pos (not_le.mp h2232).le h2223 hz1 h2237 hz
              · -- right
                exact CKLaneC2R.EpCells.B021.e1316_pos (not_le.mp h2232).le h2223 (not_le.mp h2237).le h2236 hz
            · -- right
              by_cases h2238 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1322_pos (not_le.mp h2232).le h2223 (not_le.mp h2236).le h2238 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1324_pos (not_le.mp h2232).le h2223 (not_le.mp h2238).le hz2 hz
      · -- right
        by_cases h2239 : a ≤ ((428607/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2240 : a ≤ ((171273/819200 : ℚ) : ℝ)
          · -- left
            by_cases h2241 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2242 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1325_pos (not_le.mp h2223).le h2240 hz1 h2242 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1327_pos (not_le.mp h2223).le h2240 (not_le.mp h2242).le h2241 hz
            · -- right
              by_cases h2243 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1333_pos (not_le.mp h2223).le h2240 (not_le.mp h2241).le h2243 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1335_pos (not_le.mp h2223).le h2240 (not_le.mp h2243).le hz2 hz
          · -- right
            by_cases h2244 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2245 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1326_pos (not_le.mp h2240).le h2239 hz1 h2245 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1328_pos (not_le.mp h2240).le h2239 (not_le.mp h2245).le h2244 hz
            · -- right
              by_cases h2246 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1334_pos (not_le.mp h2240).le h2239 (not_le.mp h2244).le h2246 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1336_pos (not_le.mp h2240).le h2239 (not_le.mp h2246).le hz2 hz
        · -- right
          by_cases h2247 : a ≤ ((858063/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2248 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2249 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1329_pos (not_le.mp h2239).le h2247 hz1 h2249 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1331_pos (not_le.mp h2239).le h2247 (not_le.mp h2249).le h2248 hz
            · -- right
              by_cases h2250 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1337_pos (not_le.mp h2239).le h2247 (not_le.mp h2248).le h2250 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1339_pos (not_le.mp h2239).le h2247 (not_le.mp h2250).le hz2 hz
          · -- right
            by_cases h2251 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2252 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1330_pos (not_le.mp h2247).le h2126 hz1 h2252 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1332_pos (not_le.mp h2247).le h2126 (not_le.mp h2252).le h2251 hz
            · -- right
              by_cases h2253 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1338_pos (not_le.mp h2247).le h2126 (not_le.mp h2251).le h2253 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1340_pos (not_le.mp h2247).le h2126 (not_le.mp h2253).le hz2 hz

end CKLaneC2R.EndpointCover


