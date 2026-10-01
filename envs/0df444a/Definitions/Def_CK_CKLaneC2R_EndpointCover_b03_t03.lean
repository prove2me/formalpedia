-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b03_t03
-- name    : CK_CKLaneC2R_EndpointCover_b03_t03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:56:26.408978+00:00
-- url     : https://prove2.me/theorems/9f9970f6-99bc-4e8c-bd75-d64b58d26ad2
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 4 of 6 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 4 of 6 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 4 of 6 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 4 of 6 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 4 of 6 of 3).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B009
import Definitions.Def_CK_CKLaneC2R_EpCells_B022
import Definitions.Def_CK_CKLaneC2R_EpCells_B023
namespace CKLaneC2R.EndpointCover

theorem cover_sub_017 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((3249/16000 : ℚ) : ℝ))) (h2124 : a ≤ ((7347/32000 : ℚ) : ℝ)) (h2125 : a ≤ ((2769/12800 : ℚ) : ℝ)) (h2126 : ¬ (a ≤ ((26841/128000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h2254 : a ≤ ((54531/256000 : ℚ) : ℝ)
  · -- left
    by_cases h2255 : a ≤ ((108213/512000 : ℚ) : ℝ)
    · -- left
      by_cases h2256 : a ≤ ((215577/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h2257 : a ≤ ((86061/409600 : ℚ) : ℝ)
        · -- left
          by_cases h2258 : a ≤ ((859761/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2259 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2260 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1341_pos (not_le.mp h2126).le h2258 hz1 h2260 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1343_pos (not_le.mp h2126).le h2258 (not_le.mp h2260).le h2259 hz
            · -- right
              by_cases h2261 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1349_pos (not_le.mp h2126).le h2258 (not_le.mp h2259).le h2261 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1351_pos (not_le.mp h2126).le h2258 (not_le.mp h2261).le hz2 hz
          · -- right
            by_cases h2262 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2263 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1342_pos (not_le.mp h2258).le h2257 hz1 h2263 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1344_pos (not_le.mp h2258).le h2257 (not_le.mp h2263).le h2262 hz
            · -- right
              by_cases h2264 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1350_pos (not_le.mp h2258).le h2257 (not_le.mp h2262).le h2264 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1352_pos (not_le.mp h2258).le h2257 (not_le.mp h2264).le hz2 hz
        · -- right
          by_cases h2265 : a ≤ ((861459/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2266 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2267 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1345_pos (not_le.mp h2257).le h2265 hz1 h2267 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1347_pos (not_le.mp h2257).le h2265 (not_le.mp h2267).le h2266 hz
            · -- right
              by_cases h2268 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1353_pos (not_le.mp h2257).le h2265 (not_le.mp h2266).le h2268 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1355_pos (not_le.mp h2257).le h2265 (not_le.mp h2268).le hz2 hz
          · -- right
            by_cases h2269 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2270 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1346_pos (not_le.mp h2265).le h2256 hz1 h2270 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1348_pos (not_le.mp h2265).le h2256 (not_le.mp h2270).le h2269 hz
            · -- right
              by_cases h2271 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1354_pos (not_le.mp h2265).le h2256 (not_le.mp h2269).le h2271 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1356_pos (not_le.mp h2265).le h2256 (not_le.mp h2271).le hz2 hz
      · -- right
        by_cases h2272 : a ≤ ((432003/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2273 : a ≤ ((863157/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2274 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2275 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1357_pos (not_le.mp h2256).le h2273 hz1 h2275 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1359_pos (not_le.mp h2256).le h2273 (not_le.mp h2275).le h2274 hz
            · -- right
              by_cases h2276 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1365_pos (not_le.mp h2256).le h2273 (not_le.mp h2274).le h2276 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1367_pos (not_le.mp h2256).le h2273 (not_le.mp h2276).le hz2 hz
          · -- right
            by_cases h2277 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2278 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1358_pos (not_le.mp h2273).le h2272 hz1 h2278 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1360_pos (not_le.mp h2273).le h2272 (not_le.mp h2278).le h2277 hz
            · -- right
              by_cases h2279 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1366_pos (not_le.mp h2273).le h2272 (not_le.mp h2277).le h2279 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1368_pos (not_le.mp h2273).le h2272 (not_le.mp h2279).le hz2 hz
        · -- right
          by_cases h2280 : a ≤ ((172971/819200 : ℚ) : ℝ)
          · -- left
            by_cases h2281 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2282 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1361_pos (not_le.mp h2272).le h2280 hz1 h2282 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1363_pos (not_le.mp h2272).le h2280 (not_le.mp h2282).le h2281 hz
            · -- right
              by_cases h2283 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1369_pos (not_le.mp h2272).le h2280 (not_le.mp h2281).le h2283 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1371_pos (not_le.mp h2272).le h2280 (not_le.mp h2283).le hz2 hz
          · -- right
            by_cases h2284 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2285 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1362_pos (not_le.mp h2280).le h2255 hz1 h2285 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1364_pos (not_le.mp h2280).le h2255 (not_le.mp h2285).le h2284 hz
            · -- right
              by_cases h2286 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1370_pos (not_le.mp h2280).le h2255 (not_le.mp h2284).le h2286 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1372_pos (not_le.mp h2280).le h2255 (not_le.mp h2286).le hz2 hz
    · -- right
      by_cases h2287 : a ≤ ((8691/40960 : ℚ) : ℝ)
      · -- left
        by_cases h2288 : a ≤ ((433701/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2289 : a ≤ ((866553/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2290 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2291 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1373_pos (not_le.mp h2255).le h2289 hz1 h2291 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1375_pos (not_le.mp h2255).le h2289 (not_le.mp h2291).le h2290 hz
            · -- right
              by_cases h2292 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1381_pos (not_le.mp h2255).le h2289 (not_le.mp h2290).le h2292 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1383_pos (not_le.mp h2255).le h2289 (not_le.mp h2292).le hz2 hz
          · -- right
            by_cases h2293 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2294 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1374_pos (not_le.mp h2289).le h2288 hz1 h2294 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1376_pos (not_le.mp h2289).le h2288 (not_le.mp h2294).le h2293 hz
            · -- right
              by_cases h2295 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1382_pos (not_le.mp h2289).le h2288 (not_le.mp h2293).le h2295 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1384_pos (not_le.mp h2289).le h2288 (not_le.mp h2295).le hz2 hz
        · -- right
          by_cases h2296 : a ≤ ((868251/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2297 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2298 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1377_pos (not_le.mp h2288).le h2296 hz1 h2298 hz
              · -- right
                exact CKLaneC2R.EpCells.B022.e1379_pos (not_le.mp h2288).le h2296 (not_le.mp h2298).le h2297 hz
            · -- right
              by_cases h2299 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1385_pos (not_le.mp h2288).le h2296 (not_le.mp h2297).le h2299 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1387_pos (not_le.mp h2288).le h2296 (not_le.mp h2299).le hz2 hz
          · -- right
            by_cases h2300 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2301 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B022.e1378_pos (not_le.mp h2296).le h2287 hz1 h2301 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1380_pos (not_le.mp h2296).le h2287 (not_le.mp h2301).le h2300 hz
            · -- right
              by_cases h2302 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1386_pos (not_le.mp h2296).le h2287 (not_le.mp h2300).le h2302 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1388_pos (not_le.mp h2296).le h2287 (not_le.mp h2302).le hz2 hz
      · -- right
        by_cases h2303 : a ≤ ((435399/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2304 : a ≤ ((869949/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2305 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2306 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1389_pos (not_le.mp h2287).le h2304 hz1 h2306 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1391_pos (not_le.mp h2287).le h2304 (not_le.mp h2306).le h2305 hz
            · -- right
              by_cases h2307 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1397_pos (not_le.mp h2287).le h2304 (not_le.mp h2305).le h2307 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1399_pos (not_le.mp h2287).le h2304 (not_le.mp h2307).le hz2 hz
          · -- right
            by_cases h2308 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2309 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1390_pos (not_le.mp h2304).le h2303 hz1 h2309 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1392_pos (not_le.mp h2304).le h2303 (not_le.mp h2309).le h2308 hz
            · -- right
              by_cases h2310 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1398_pos (not_le.mp h2304).le h2303 (not_le.mp h2308).le h2310 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1400_pos (not_le.mp h2304).le h2303 (not_le.mp h2310).le hz2 hz
        · -- right
          by_cases h2311 : a ≤ ((871647/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h2312 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2313 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1393_pos (not_le.mp h2303).le h2311 hz1 h2313 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1395_pos (not_le.mp h2303).le h2311 (not_le.mp h2313).le h2312 hz
            · -- right
              by_cases h2314 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1401_pos (not_le.mp h2303).le h2311 (not_le.mp h2312).le h2314 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1403_pos (not_le.mp h2303).le h2311 (not_le.mp h2314).le hz2 hz
          · -- right
            by_cases h2315 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2316 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1394_pos (not_le.mp h2311).le h2254 hz1 h2316 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1396_pos (not_le.mp h2311).le h2254 (not_le.mp h2316).le h2315 hz
            · -- right
              by_cases h2317 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1402_pos (not_le.mp h2311).le h2254 (not_le.mp h2315).le h2317 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1404_pos (not_le.mp h2311).le h2254 (not_le.mp h2317).le hz2 hz
  · -- right
    by_cases h2318 : a ≤ ((109911/512000 : ℚ) : ℝ)
    · -- left
      by_cases h2319 : a ≤ ((218973/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h2320 : a ≤ ((437097/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2321 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h2322 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e544_pos (not_le.mp h2254).le h2320 hz1 h2322 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e545_pos (not_le.mp h2254).le h2320 (not_le.mp h2322).le h2321 hz
          · -- right
            by_cases h2323 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e548_pos (not_le.mp h2254).le h2320 (not_le.mp h2321).le h2323 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e549_pos (not_le.mp h2254).le h2320 (not_le.mp h2323).le hz2 hz
        · -- right
          by_cases h2324 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h2325 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e546_pos (not_le.mp h2320).le h2319 hz1 h2325 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e547_pos (not_le.mp h2320).le h2319 (not_le.mp h2325).le h2324 hz
          · -- right
            by_cases h2326 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e550_pos (not_le.mp h2320).le h2319 (not_le.mp h2324).le h2326 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e551_pos (not_le.mp h2320).le h2319 (not_le.mp h2326).le hz2 hz
      · -- right
        by_cases h2327 : a ≤ ((87759/409600 : ℚ) : ℝ)
        · -- left
          by_cases h2328 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h2329 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e552_pos (not_le.mp h2319).le h2327 hz1 h2329 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e553_pos (not_le.mp h2319).le h2327 (not_le.mp h2329).le h2328 hz
          · -- right
            by_cases h2330 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e556_pos (not_le.mp h2319).le h2327 (not_le.mp h2328).le h2330 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e557_pos (not_le.mp h2319).le h2327 (not_le.mp h2330).le hz2 hz
        · -- right
          by_cases h2331 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h2332 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e554_pos (not_le.mp h2327).le h2318 hz1 h2332 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e555_pos (not_le.mp h2327).le h2318 (not_le.mp h2332).le h2331 hz
          · -- right
            by_cases h2333 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e558_pos (not_le.mp h2327).le h2318 (not_le.mp h2331).le h2333 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e559_pos (not_le.mp h2327).le h2318 (not_le.mp h2333).le hz2 hz
    · -- right
      by_cases h2334 : a ≤ ((220671/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h2335 : a ≤ ((440493/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2336 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h2337 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e560_pos (not_le.mp h2318).le h2335 hz1 h2337 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e561_pos (not_le.mp h2318).le h2335 (not_le.mp h2337).le h2336 hz
          · -- right
            by_cases h2338 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e564_pos (not_le.mp h2318).le h2335 (not_le.mp h2336).le h2338 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e565_pos (not_le.mp h2318).le h2335 (not_le.mp h2338).le hz2 hz
        · -- right
          by_cases h2339 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h2340 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e562_pos (not_le.mp h2335).le h2334 hz1 h2340 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e563_pos (not_le.mp h2335).le h2334 (not_le.mp h2340).le h2339 hz
          · -- right
            by_cases h2341 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e566_pos (not_le.mp h2335).le h2334 (not_le.mp h2339).le h2341 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e567_pos (not_le.mp h2335).le h2334 (not_le.mp h2341).le hz2 hz
      · -- right
        by_cases h2342 : a ≤ ((442191/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h2343 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h2344 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e568_pos (not_le.mp h2334).le h2342 hz1 h2344 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e569_pos (not_le.mp h2334).le h2342 (not_le.mp h2344).le h2343 hz
          · -- right
            by_cases h2345 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e572_pos (not_le.mp h2334).le h2342 (not_le.mp h2343).le h2345 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e573_pos (not_le.mp h2334).le h2342 (not_le.mp h2345).le hz2 hz
        · -- right
          by_cases h2346 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h2347 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e570_pos (not_le.mp h2342).le h2125 hz1 h2347 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e571_pos (not_le.mp h2342).le h2125 (not_le.mp h2347).le h2346 hz
          · -- right
            by_cases h2348 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B009.e574_pos (not_le.mp h2342).le h2125 (not_le.mp h2346).le h2348 hz
            · -- right
              exact CKLaneC2R.EpCells.B009.e575_pos (not_le.mp h2342).le h2125 (not_le.mp h2348).le hz2 hz

end CKLaneC2R.EndpointCover


