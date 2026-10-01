-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b02
-- name    : CK_CKLaneC2R_EndpointCover_b02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:06:41.7493+00:00
-- url     : https://prove2.me/theorems/916edd0f-5e54-42e9-bd28-e154e8026fc4
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 3 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 3 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 3 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 3 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 3 of 5).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B023
import Definitions.Def_CK_CKLaneC2R_EpCells_B024
import Definitions.Def_CK_CKLaneC2R_EpCells_B046
import Definitions.Def_CK_CKLaneC2R_EpCells_B047
import Definitions.Def_CK_CKLaneC2R_EpCells_B048
namespace CKLaneC2R.EndpointCover

theorem cover_sub_010 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : ¬ (a ≤ ((10449/64000 : ℚ) : ℝ))) (h1029 : a ≤ ((21747/128000 : ℚ) : ℝ)) (h1030 : ¬ (a ≤ ((8529/51200 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1286 : a ≤ ((86139/512000 : ℚ) : ℝ)
  · -- left
    by_cases h1287 : a ≤ ((171429/1024000 : ℚ) : ℝ)
    · -- left
      by_cases h1288 : a ≤ ((342009/2048000 : ℚ) : ℝ)
      · -- left
        by_cases h1289 : a ≤ ((683169/4096000 : ℚ) : ℝ)
        · -- left
          by_cases h1290 : a ≤ ((1365489/8192000 : ℚ) : ℝ)
          · -- left
            by_cases h1291 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1292 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1293 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B046.e2808_pos (not_le.mp h1030).le h1290 hz1 h1293 hz
                · -- right
                  exact CKLaneC2R.EpCells.B046.e2810_pos (not_le.mp h1030).le h1290 (not_le.mp h1293).le h1292 hz
              · -- right
                by_cases h1294 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B046.e2816_pos (not_le.mp h1030).le h1290 (not_le.mp h1292).le h1294 hz
                · -- right
                  exact CKLaneC2R.EpCells.B046.e2818_pos (not_le.mp h1030).le h1290 (not_le.mp h1294).le h1291 hz
            · -- right
              by_cases h1295 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1296 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2840_pos (not_le.mp h1030).le h1290 (not_le.mp h1291).le h1296 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2842_pos (not_le.mp h1030).le h1290 (not_le.mp h1296).le h1295 hz
              · -- right
                by_cases h1297 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2848_pos (not_le.mp h1030).le h1290 (not_le.mp h1295).le h1297 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2850_pos (not_le.mp h1030).le h1290 (not_le.mp h1297).le hz2 hz
          · -- right
            by_cases h1298 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1299 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1300 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B046.e2809_pos (not_le.mp h1290).le h1289 hz1 h1300 hz
                · -- right
                  exact CKLaneC2R.EpCells.B046.e2811_pos (not_le.mp h1290).le h1289 (not_le.mp h1300).le h1299 hz
              · -- right
                by_cases h1301 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B046.e2817_pos (not_le.mp h1290).le h1289 (not_le.mp h1299).le h1301 hz
                · -- right
                  exact CKLaneC2R.EpCells.B046.e2819_pos (not_le.mp h1290).le h1289 (not_le.mp h1301).le h1298 hz
            · -- right
              by_cases h1302 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1303 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2841_pos (not_le.mp h1290).le h1289 (not_le.mp h1298).le h1303 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2843_pos (not_le.mp h1290).le h1289 (not_le.mp h1303).le h1302 hz
              · -- right
                by_cases h1304 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2849_pos (not_le.mp h1290).le h1289 (not_le.mp h1302).le h1304 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2851_pos (not_le.mp h1290).le h1289 (not_le.mp h1304).le hz2 hz
        · -- right
          by_cases h1305 : a ≤ ((1367187/8192000 : ℚ) : ℝ)
          · -- left
            by_cases h1306 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1307 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1308 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B046.e2812_pos (not_le.mp h1289).le h1305 hz1 h1308 hz
                · -- right
                  exact CKLaneC2R.EpCells.B046.e2814_pos (not_le.mp h1289).le h1305 (not_le.mp h1308).le h1307 hz
              · -- right
                by_cases h1309 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2820_pos (not_le.mp h1289).le h1305 (not_le.mp h1307).le h1309 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2822_pos (not_le.mp h1289).le h1305 (not_le.mp h1309).le h1306 hz
            · -- right
              by_cases h1310 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1311 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2844_pos (not_le.mp h1289).le h1305 (not_le.mp h1306).le h1311 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2846_pos (not_le.mp h1289).le h1305 (not_le.mp h1311).le h1310 hz
              · -- right
                by_cases h1312 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2852_pos (not_le.mp h1289).le h1305 (not_le.mp h1310).le h1312 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2854_pos (not_le.mp h1289).le h1305 (not_le.mp h1312).le hz2 hz
          · -- right
            by_cases h1313 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1314 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1315 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B046.e2813_pos (not_le.mp h1305).le h1288 hz1 h1315 hz
                · -- right
                  exact CKLaneC2R.EpCells.B046.e2815_pos (not_le.mp h1305).le h1288 (not_le.mp h1315).le h1314 hz
              · -- right
                by_cases h1316 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2821_pos (not_le.mp h1305).le h1288 (not_le.mp h1314).le h1316 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2823_pos (not_le.mp h1305).le h1288 (not_le.mp h1316).le h1313 hz
            · -- right
              by_cases h1317 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1318 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2845_pos (not_le.mp h1305).le h1288 (not_le.mp h1313).le h1318 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2847_pos (not_le.mp h1305).le h1288 (not_le.mp h1318).le h1317 hz
              · -- right
                by_cases h1319 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2853_pos (not_le.mp h1305).le h1288 (not_le.mp h1317).le h1319 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2855_pos (not_le.mp h1305).le h1288 (not_le.mp h1319).le hz2 hz
      · -- right
        by_cases h1320 : a ≤ ((684867/4096000 : ℚ) : ℝ)
        · -- left
          by_cases h1321 : a ≤ ((273777/1638400 : ℚ) : ℝ)
          · -- left
            by_cases h1322 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1323 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1324 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2824_pos (not_le.mp h1288).le h1321 hz1 h1324 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2826_pos (not_le.mp h1288).le h1321 (not_le.mp h1324).le h1323 hz
              · -- right
                by_cases h1325 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2832_pos (not_le.mp h1288).le h1321 (not_le.mp h1323).le h1325 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2834_pos (not_le.mp h1288).le h1321 (not_le.mp h1325).le h1322 hz
            · -- right
              by_cases h1326 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1327 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2856_pos (not_le.mp h1288).le h1321 (not_le.mp h1322).le h1327 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2858_pos (not_le.mp h1288).le h1321 (not_le.mp h1327).le h1326 hz
              · -- right
                by_cases h1328 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2864_pos (not_le.mp h1288).le h1321 (not_le.mp h1326).le h1328 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2866_pos (not_le.mp h1288).le h1321 (not_le.mp h1328).le hz2 hz
          · -- right
            by_cases h1329 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1330 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1331 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2825_pos (not_le.mp h1321).le h1320 hz1 h1331 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2827_pos (not_le.mp h1321).le h1320 (not_le.mp h1331).le h1330 hz
              · -- right
                by_cases h1332 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2833_pos (not_le.mp h1321).le h1320 (not_le.mp h1330).le h1332 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2835_pos (not_le.mp h1321).le h1320 (not_le.mp h1332).le h1329 hz
            · -- right
              by_cases h1333 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1334 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2857_pos (not_le.mp h1321).le h1320 (not_le.mp h1329).le h1334 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2859_pos (not_le.mp h1321).le h1320 (not_le.mp h1334).le h1333 hz
              · -- right
                by_cases h1335 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2865_pos (not_le.mp h1321).le h1320 (not_le.mp h1333).le h1335 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2867_pos (not_le.mp h1321).le h1320 (not_le.mp h1335).le hz2 hz
        · -- right
          by_cases h1336 : a ≤ ((1370583/8192000 : ℚ) : ℝ)
          · -- left
            by_cases h1337 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1338 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1339 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2828_pos (not_le.mp h1320).le h1336 hz1 h1339 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2830_pos (not_le.mp h1320).le h1336 (not_le.mp h1339).le h1338 hz
              · -- right
                by_cases h1340 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2836_pos (not_le.mp h1320).le h1336 (not_le.mp h1338).le h1340 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2838_pos (not_le.mp h1320).le h1336 (not_le.mp h1340).le h1337 hz
            · -- right
              by_cases h1341 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1342 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2860_pos (not_le.mp h1320).le h1336 (not_le.mp h1337).le h1342 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2862_pos (not_le.mp h1320).le h1336 (not_le.mp h1342).le h1341 hz
              · -- right
                by_cases h1343 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2868_pos (not_le.mp h1320).le h1336 (not_le.mp h1341).le h1343 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2870_pos (not_le.mp h1320).le h1336 (not_le.mp h1343).le hz2 hz
          · -- right
            by_cases h1344 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1345 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1346 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2829_pos (not_le.mp h1336).le h1287 hz1 h1346 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2831_pos (not_le.mp h1336).le h1287 (not_le.mp h1346).le h1345 hz
              · -- right
                by_cases h1347 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2837_pos (not_le.mp h1336).le h1287 (not_le.mp h1345).le h1347 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2839_pos (not_le.mp h1336).le h1287 (not_le.mp h1347).le h1344 hz
            · -- right
              by_cases h1348 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1349 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2861_pos (not_le.mp h1336).le h1287 (not_le.mp h1344).le h1349 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2863_pos (not_le.mp h1336).le h1287 (not_le.mp h1349).le h1348 hz
              · -- right
                by_cases h1350 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2869_pos (not_le.mp h1336).le h1287 (not_le.mp h1348).le h1350 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2871_pos (not_le.mp h1336).le h1287 (not_le.mp h1350).le hz2 hz
    · -- right
      by_cases h1351 : a ≤ ((343707/2048000 : ℚ) : ℝ)
      · -- left
        by_cases h1352 : a ≤ ((137313/819200 : ℚ) : ℝ)
        · -- left
          by_cases h1353 : a ≤ ((1372281/8192000 : ℚ) : ℝ)
          · -- left
            by_cases h1354 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1355 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1356 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2872_pos (not_le.mp h1287).le h1353 hz1 h1356 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2874_pos (not_le.mp h1287).le h1353 (not_le.mp h1356).le h1355 hz
              · -- right
                by_cases h1357 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2880_pos (not_le.mp h1287).le h1353 (not_le.mp h1355).le h1357 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2882_pos (not_le.mp h1287).le h1353 (not_le.mp h1357).le h1354 hz
            · -- right
              by_cases h1358 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1359 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2896_pos (not_le.mp h1287).le h1353 (not_le.mp h1354).le h1359 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2898_pos (not_le.mp h1287).le h1353 (not_le.mp h1359).le h1358 hz
              · -- right
                by_cases h1360 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2904_pos (not_le.mp h1287).le h1353 (not_le.mp h1358).le h1360 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2906_pos (not_le.mp h1287).le h1353 (not_le.mp h1360).le hz2 hz
          · -- right
            by_cases h1361 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1362 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1363 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2873_pos (not_le.mp h1353).le h1352 hz1 h1363 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2875_pos (not_le.mp h1353).le h1352 (not_le.mp h1363).le h1362 hz
              · -- right
                by_cases h1364 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2881_pos (not_le.mp h1353).le h1352 (not_le.mp h1362).le h1364 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2883_pos (not_le.mp h1353).le h1352 (not_le.mp h1364).le h1361 hz
            · -- right
              by_cases h1365 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1366 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2897_pos (not_le.mp h1353).le h1352 (not_le.mp h1361).le h1366 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2899_pos (not_le.mp h1353).le h1352 (not_le.mp h1366).le h1365 hz
              · -- right
                by_cases h1367 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2905_pos (not_le.mp h1353).le h1352 (not_le.mp h1365).le h1367 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2907_pos (not_le.mp h1353).le h1352 (not_le.mp h1367).le hz2 hz
        · -- right
          by_cases h1368 : a ≤ ((1373979/8192000 : ℚ) : ℝ)
          · -- left
            by_cases h1369 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1370 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1371 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2876_pos (not_le.mp h1352).le h1368 hz1 h1371 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2878_pos (not_le.mp h1352).le h1368 (not_le.mp h1371).le h1370 hz
              · -- right
                by_cases h1372 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2884_pos (not_le.mp h1352).le h1368 (not_le.mp h1370).le h1372 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2886_pos (not_le.mp h1352).le h1368 (not_le.mp h1372).le h1369 hz
            · -- right
              by_cases h1373 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1374 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2900_pos (not_le.mp h1352).le h1368 (not_le.mp h1369).le h1374 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2902_pos (not_le.mp h1352).le h1368 (not_le.mp h1374).le h1373 hz
              · -- right
                by_cases h1375 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2908_pos (not_le.mp h1352).le h1368 (not_le.mp h1373).le h1375 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2910_pos (not_le.mp h1352).le h1368 (not_le.mp h1375).le hz2 hz
          · -- right
            by_cases h1376 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1377 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1378 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B047.e2877_pos (not_le.mp h1368).le h1351 hz1 h1378 hz
                · -- right
                  exact CKLaneC2R.EpCells.B047.e2879_pos (not_le.mp h1368).le h1351 (not_le.mp h1378).le h1377 hz
              · -- right
                by_cases h1379 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2885_pos (not_le.mp h1368).le h1351 (not_le.mp h1377).le h1379 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2887_pos (not_le.mp h1368).le h1351 (not_le.mp h1379).le h1376 hz
            · -- right
              by_cases h1380 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1381 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2901_pos (not_le.mp h1368).le h1351 (not_le.mp h1376).le h1381 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2903_pos (not_le.mp h1368).le h1351 (not_le.mp h1381).le h1380 hz
              · -- right
                by_cases h1382 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2909_pos (not_le.mp h1368).le h1351 (not_le.mp h1380).le h1382 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2911_pos (not_le.mp h1368).le h1351 (not_le.mp h1382).le hz2 hz
      · -- right
        by_cases h1383 : a ≤ ((688263/4096000 : ℚ) : ℝ)
        · -- left
          by_cases h1384 : a ≤ ((1375677/8192000 : ℚ) : ℝ)
          · -- left
            by_cases h1385 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1386 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1387 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2888_pos (not_le.mp h1351).le h1384 hz1 h1387 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2890_pos (not_le.mp h1351).le h1384 (not_le.mp h1387).le h1386 hz
              · -- right
                by_cases h1388 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2892_pos (not_le.mp h1351).le h1384 (not_le.mp h1386).le h1388 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2894_pos (not_le.mp h1351).le h1384 (not_le.mp h1388).le h1385 hz
            · -- right
              by_cases h1389 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1390 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2912_pos (not_le.mp h1351).le h1384 (not_le.mp h1385).le h1390 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2914_pos (not_le.mp h1351).le h1384 (not_le.mp h1390).le h1389 hz
              · -- right
                by_cases h1391 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2916_pos (not_le.mp h1351).le h1384 (not_le.mp h1389).le h1391 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2918_pos (not_le.mp h1351).le h1384 (not_le.mp h1391).le hz2 hz
          · -- right
            by_cases h1392 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1393 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1394 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2889_pos (not_le.mp h1384).le h1383 hz1 h1394 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2891_pos (not_le.mp h1384).le h1383 (not_le.mp h1394).le h1393 hz
              · -- right
                by_cases h1395 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2893_pos (not_le.mp h1384).le h1383 (not_le.mp h1393).le h1395 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2895_pos (not_le.mp h1384).le h1383 (not_le.mp h1395).le h1392 hz
            · -- right
              by_cases h1396 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1397 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2913_pos (not_le.mp h1384).le h1383 (not_le.mp h1392).le h1397 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2915_pos (not_le.mp h1384).le h1383 (not_le.mp h1397).le h1396 hz
              · -- right
                by_cases h1398 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B048.e2917_pos (not_le.mp h1384).le h1383 (not_le.mp h1396).le h1398 hz
                · -- right
                  exact CKLaneC2R.EpCells.B048.e2919_pos (not_le.mp h1384).le h1383 (not_le.mp h1398).le hz2 hz
        · -- right
          by_cases h1399 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1400 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1401 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1419_pos (not_le.mp h1383).le h1286 hz1 h1401 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1420_pos (not_le.mp h1383).le h1286 (not_le.mp h1401).le h1400 hz
            · -- right
              by_cases h1402 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1421_pos (not_le.mp h1383).le h1286 (not_le.mp h1400).le h1402 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1422_pos (not_le.mp h1383).le h1286 (not_le.mp h1402).le h1399 hz
          · -- right
            by_cases h1403 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1404 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1423_pos (not_le.mp h1383).le h1286 (not_le.mp h1399).le h1404 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1424_pos (not_le.mp h1383).le h1286 (not_le.mp h1404).le h1403 hz
            · -- right
              by_cases h1405 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1425_pos (not_le.mp h1383).le h1286 (not_le.mp h1403).le h1405 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1426_pos (not_le.mp h1383).le h1286 (not_le.mp h1405).le hz2 hz
  · -- right
    by_cases h1406 : a ≤ ((173127/1024000 : ℚ) : ℝ)
    · -- left
      by_cases h1407 : a ≤ ((69081/409600 : ℚ) : ℝ)
      · -- left
        by_cases h1408 : a ≤ ((689961/4096000 : ℚ) : ℝ)
        · -- left
          by_cases h1409 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1410 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1411 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1427_pos (not_le.mp h1286).le h1408 hz1 h1411 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1428_pos (not_le.mp h1286).le h1408 (not_le.mp h1411).le h1410 hz
            · -- right
              by_cases h1412 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1431_pos (not_le.mp h1286).le h1408 (not_le.mp h1410).le h1412 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1432_pos (not_le.mp h1286).le h1408 (not_le.mp h1412).le h1409 hz
          · -- right
            by_cases h1413 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1414 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1443_pos (not_le.mp h1286).le h1408 (not_le.mp h1409).le h1414 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1444_pos (not_le.mp h1286).le h1408 (not_le.mp h1414).le h1413 hz
            · -- right
              by_cases h1415 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1447_pos (not_le.mp h1286).le h1408 (not_le.mp h1413).le h1415 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1448_pos (not_le.mp h1286).le h1408 (not_le.mp h1415).le hz2 hz
        · -- right
          by_cases h1416 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1417 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1418 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1429_pos (not_le.mp h1408).le h1407 hz1 h1418 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1430_pos (not_le.mp h1408).le h1407 (not_le.mp h1418).le h1417 hz
            · -- right
              by_cases h1419 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1433_pos (not_le.mp h1408).le h1407 (not_le.mp h1417).le h1419 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1434_pos (not_le.mp h1408).le h1407 (not_le.mp h1419).le h1416 hz
          · -- right
            by_cases h1420 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1421 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1445_pos (not_le.mp h1408).le h1407 (not_le.mp h1416).le h1421 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1446_pos (not_le.mp h1408).le h1407 (not_le.mp h1421).le h1420 hz
            · -- right
              by_cases h1422 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1449_pos (not_le.mp h1408).le h1407 (not_le.mp h1420).le h1422 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1450_pos (not_le.mp h1408).le h1407 (not_le.mp h1422).le hz2 hz
      · -- right
        by_cases h1423 : a ≤ ((691659/4096000 : ℚ) : ℝ)
        · -- left
          by_cases h1424 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1425 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1426 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1435_pos (not_le.mp h1407).le h1423 hz1 h1426 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1436_pos (not_le.mp h1407).le h1423 (not_le.mp h1426).le h1425 hz
            · -- right
              by_cases h1427 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1439_pos (not_le.mp h1407).le h1423 (not_le.mp h1425).le h1427 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1440_pos (not_le.mp h1407).le h1423 (not_le.mp h1427).le h1424 hz
          · -- right
            by_cases h1428 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1429 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1451_pos (not_le.mp h1407).le h1423 (not_le.mp h1424).le h1429 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1452_pos (not_le.mp h1407).le h1423 (not_le.mp h1429).le h1428 hz
            · -- right
              by_cases h1430 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1455_pos (not_le.mp h1407).le h1423 (not_le.mp h1428).le h1430 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1456_pos (not_le.mp h1407).le h1423 (not_le.mp h1430).le hz2 hz
        · -- right
          by_cases h1431 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1432 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1433 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B023.e1437_pos (not_le.mp h1423).le h1406 hz1 h1433 hz
              · -- right
                exact CKLaneC2R.EpCells.B023.e1438_pos (not_le.mp h1423).le h1406 (not_le.mp h1433).le h1432 hz
            · -- right
              by_cases h1434 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1441_pos (not_le.mp h1423).le h1406 (not_le.mp h1432).le h1434 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1442_pos (not_le.mp h1423).le h1406 (not_le.mp h1434).le h1431 hz
          · -- right
            by_cases h1435 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1436 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1453_pos (not_le.mp h1423).le h1406 (not_le.mp h1431).le h1436 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1454_pos (not_le.mp h1423).le h1406 (not_le.mp h1436).le h1435 hz
            · -- right
              by_cases h1437 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1457_pos (not_le.mp h1423).le h1406 (not_le.mp h1435).le h1437 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1458_pos (not_le.mp h1423).le h1406 (not_le.mp h1437).le hz2 hz
    · -- right
      by_cases h1438 : a ≤ ((347103/2048000 : ℚ) : ℝ)
      · -- left
        by_cases h1439 : a ≤ ((693357/4096000 : ℚ) : ℝ)
        · -- left
          by_cases h1440 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1441 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1442 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1459_pos (not_le.mp h1406).le h1439 hz1 h1442 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1460_pos (not_le.mp h1406).le h1439 (not_le.mp h1442).le h1441 hz
            · -- right
              by_cases h1443 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1463_pos (not_le.mp h1406).le h1439 (not_le.mp h1441).le h1443 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1464_pos (not_le.mp h1406).le h1439 (not_le.mp h1443).le h1440 hz
          · -- right
            by_cases h1444 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1445 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1475_pos (not_le.mp h1406).le h1439 (not_le.mp h1440).le h1445 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1476_pos (not_le.mp h1406).le h1439 (not_le.mp h1445).le h1444 hz
            · -- right
              by_cases h1446 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1479_pos (not_le.mp h1406).le h1439 (not_le.mp h1444).le h1446 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1480_pos (not_le.mp h1406).le h1439 (not_le.mp h1446).le hz2 hz
        · -- right
          by_cases h1447 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1448 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1449 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1461_pos (not_le.mp h1439).le h1438 hz1 h1449 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1462_pos (not_le.mp h1439).le h1438 (not_le.mp h1449).le h1448 hz
            · -- right
              by_cases h1450 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1465_pos (not_le.mp h1439).le h1438 (not_le.mp h1448).le h1450 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1466_pos (not_le.mp h1439).le h1438 (not_le.mp h1450).le h1447 hz
          · -- right
            by_cases h1451 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1452 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1477_pos (not_le.mp h1439).le h1438 (not_le.mp h1447).le h1452 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1478_pos (not_le.mp h1439).le h1438 (not_le.mp h1452).le h1451 hz
            · -- right
              by_cases h1453 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1481_pos (not_le.mp h1439).le h1438 (not_le.mp h1451).le h1453 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1482_pos (not_le.mp h1439).le h1438 (not_le.mp h1453).le hz2 hz
      · -- right
        by_cases h1454 : a ≤ ((139011/819200 : ℚ) : ℝ)
        · -- left
          by_cases h1455 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1456 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1457 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1467_pos (not_le.mp h1438).le h1454 hz1 h1457 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1468_pos (not_le.mp h1438).le h1454 (not_le.mp h1457).le h1456 hz
            · -- right
              by_cases h1458 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1471_pos (not_le.mp h1438).le h1454 (not_le.mp h1456).le h1458 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1472_pos (not_le.mp h1438).le h1454 (not_le.mp h1458).le h1455 hz
          · -- right
            by_cases h1459 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1460 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1483_pos (not_le.mp h1438).le h1454 (not_le.mp h1455).le h1460 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1484_pos (not_le.mp h1438).le h1454 (not_le.mp h1460).le h1459 hz
            · -- right
              by_cases h1461 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1487_pos (not_le.mp h1438).le h1454 (not_le.mp h1459).le h1461 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1488_pos (not_le.mp h1438).le h1454 (not_le.mp h1461).le hz2 hz
        · -- right
          by_cases h1462 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1463 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1464 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1469_pos (not_le.mp h1454).le h1029 hz1 h1464 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1470_pos (not_le.mp h1454).le h1029 (not_le.mp h1464).le h1463 hz
            · -- right
              by_cases h1465 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1473_pos (not_le.mp h1454).le h1029 (not_le.mp h1463).le h1465 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1474_pos (not_le.mp h1454).le h1029 (not_le.mp h1465).le h1462 hz
          · -- right
            by_cases h1466 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1467 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1485_pos (not_le.mp h1454).le h1029 (not_le.mp h1462).le h1467 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1486_pos (not_le.mp h1454).le h1029 (not_le.mp h1467).le h1466 hz
            · -- right
              by_cases h1468 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B024.e1489_pos (not_le.mp h1454).le h1029 (not_le.mp h1466).le h1468 hz
              · -- right
                exact CKLaneC2R.EpCells.B024.e1490_pos (not_le.mp h1454).le h1029 (not_le.mp h1468).le hz2 hz

end CKLaneC2R.EndpointCover


