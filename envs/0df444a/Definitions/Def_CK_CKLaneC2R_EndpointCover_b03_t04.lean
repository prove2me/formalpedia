-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b03_t04
-- name    : CK_CKLaneC2R_EndpointCover_b03_t04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:05:01.197769+00:00
-- url     : https://prove2.me/theorems/195c3223-7129-4683-a7b9-97ad2f759552
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 5 of 6 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 5 of 6 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 5 of 6 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 5 of 6 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 5 of 6 of 3).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B003__2
import Definitions.Def_CK_CKLaneC2R_EpCells_B005
import Definitions.Def_CK_CKLaneC2R_EpCells_B009
namespace CKLaneC2R.EndpointCover

theorem cover_sub_018 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((3249/16000 : ℚ) : ℝ))) (h2124 : a ≤ ((7347/32000 : ℚ) : ℝ)) (h2125 : ¬ (a ≤ ((2769/12800 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h2349 : a ≤ ((28539/128000 : ℚ) : ℝ)
  · -- left
    by_cases h2350 : a ≤ ((56229/256000 : ℚ) : ℝ)
    · -- left
      by_cases h2351 : a ≤ ((111609/512000 : ℚ) : ℝ)
      · -- left
        by_cases h2352 : a ≤ ((222369/1024000 : ℚ) : ℝ)
        · -- left
          by_cases h2353 : a ≤ ((443889/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2354 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2355 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B009.e576_pos (not_le.mp h2125).le h2353 hz1 h2355 hz
              · -- right
                exact CKLaneC2R.EpCells.B009.e577_pos (not_le.mp h2125).le h2353 (not_le.mp h2355).le h2354 hz
            · -- right
              by_cases h2356 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B009.e580_pos (not_le.mp h2125).le h2353 (not_le.mp h2354).le h2356 hz
              · -- right
                exact CKLaneC2R.EpCells.B009.e581_pos (not_le.mp h2125).le h2353 (not_le.mp h2356).le hz2 hz
          · -- right
            by_cases h2357 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h2358 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B009.e578_pos (not_le.mp h2353).le h2352 hz1 h2358 hz
              · -- right
                exact CKLaneC2R.EpCells.B009.e579_pos (not_le.mp h2353).le h2352 (not_le.mp h2358).le h2357 hz
            · -- right
              by_cases h2359 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B009.e582_pos (not_le.mp h2353).le h2352 (not_le.mp h2357).le h2359 hz
              · -- right
                exact CKLaneC2R.EpCells.B009.e583_pos (not_le.mp h2353).le h2352 (not_le.mp h2359).le hz2 hz
        · -- right
          by_cases h2360 : a ≤ ((445587/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2361 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e275_pos (not_le.mp h2352).le h2360 hz1 h2361 hz
            · -- right
              by_cases h2362 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B009.e584_pos (not_le.mp h2352).le h2360 (not_le.mp h2361).le h2362 hz
              · -- right
                exact CKLaneC2R.EpCells.B009.e585_pos (not_le.mp h2352).le h2360 (not_le.mp h2362).le hz2 hz
          · -- right
            by_cases h2363 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e276_pos (not_le.mp h2360).le h2351 hz1 h2363 hz
            · -- right
              exact CKLaneC2R.EpCells.B004.e277_pos (not_le.mp h2360).le h2351 (not_le.mp h2363).le hz2 hz
      · -- right
        by_cases h2364 : a ≤ ((224067/1024000 : ℚ) : ℝ)
        · -- left
          by_cases h2365 : a ≤ ((89457/409600 : ℚ) : ℝ)
          · -- left
            by_cases h2366 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e278_pos (not_le.mp h2351).le h2365 hz1 h2366 hz
            · -- right
              exact CKLaneC2R.EpCells.B004.e280_pos (not_le.mp h2351).le h2365 (not_le.mp h2366).le hz2 hz
          · -- right
            by_cases h2367 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e279_pos (not_le.mp h2365).le h2364 hz1 h2367 hz
            · -- right
              exact CKLaneC2R.EpCells.B004.e281_pos (not_le.mp h2365).le h2364 (not_le.mp h2367).le hz2 hz
        · -- right
          by_cases h2368 : a ≤ ((448983/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2369 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e282_pos (not_le.mp h2364).le h2368 hz1 h2369 hz
            · -- right
              exact CKLaneC2R.EpCells.B004.e284_pos (not_le.mp h2364).le h2368 (not_le.mp h2369).le hz2 hz
          · -- right
            by_cases h2370 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e283_pos (not_le.mp h2368).le h2350 hz1 h2370 hz
            · -- right
              exact CKLaneC2R.EpCells.B004.e285_pos (not_le.mp h2368).le h2350 (not_le.mp h2370).le hz2 hz
    · -- right
      by_cases h2371 : a ≤ ((113307/512000 : ℚ) : ℝ)
      · -- left
        by_cases h2372 : a ≤ ((45153/204800 : ℚ) : ℝ)
        · -- left
          by_cases h2373 : a ≤ ((450681/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2374 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e286_pos (not_le.mp h2350).le h2373 hz1 h2374 hz
            · -- right
              exact CKLaneC2R.EpCells.B004.e288_pos (not_le.mp h2350).le h2373 (not_le.mp h2374).le hz2 hz
          · -- right
            by_cases h2375 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e287_pos (not_le.mp h2373).le h2372 hz1 h2375 hz
            · -- right
              exact CKLaneC2R.EpCells.B004.e289_pos (not_le.mp h2373).le h2372 (not_le.mp h2375).le hz2 hz
        · -- right
          by_cases h2376 : a ≤ ((452379/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2377 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e290_pos (not_le.mp h2372).le h2376 hz1 h2377 hz
            · -- right
              exact CKLaneC2R.EpCells.B004.e292_pos (not_le.mp h2372).le h2376 (not_le.mp h2377).le hz2 hz
          · -- right
            by_cases h2378 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e291_pos (not_le.mp h2376).le h2371 hz1 h2378 hz
            · -- right
              exact CKLaneC2R.EpCells.B004.e293_pos (not_le.mp h2376).le h2371 (not_le.mp h2378).le hz2 hz
      · -- right
        by_cases h2379 : a ≤ ((227463/1024000 : ℚ) : ℝ)
        · -- left
          by_cases h2380 : a ≤ ((454077/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2381 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e294_pos (not_le.mp h2371).le h2380 hz1 h2381 hz
            · -- right
              exact CKLaneC2R.EpCells.B004.e296_pos (not_le.mp h2371).le h2380 (not_le.mp h2381).le hz2 hz
          · -- right
            by_cases h2382 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e295_pos (not_le.mp h2380).le h2379 hz1 h2382 hz
            · -- right
              exact CKLaneC2R.EpCells.B004.e297_pos (not_le.mp h2380).le h2379 (not_le.mp h2382).le hz2 hz
        · -- right
          by_cases h2383 : a ≤ ((18231/81920 : ℚ) : ℝ)
          · -- left
            by_cases h2384 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e298_pos (not_le.mp h2379).le h2383 hz1 h2384 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e300_pos (not_le.mp h2379).le h2383 (not_le.mp h2384).le hz2 hz
          · -- right
            by_cases h2385 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B004.e299_pos (not_le.mp h2383).le h2349 hz1 h2385 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e301_pos (not_le.mp h2383).le h2349 (not_le.mp h2385).le hz2 hz
  · -- right
    by_cases h2386 : a ≤ ((57927/256000 : ℚ) : ℝ)
    · -- left
      by_cases h2387 : a ≤ ((23001/102400 : ℚ) : ℝ)
      · -- left
        by_cases h2388 : a ≤ ((229161/1024000 : ℚ) : ℝ)
        · -- left
          by_cases h2389 : a ≤ ((457473/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2390 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e302_pos (not_le.mp h2349).le h2389 hz1 h2390 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e304_pos (not_le.mp h2349).le h2389 (not_le.mp h2390).le hz2 hz
          · -- right
            by_cases h2391 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e303_pos (not_le.mp h2389).le h2388 hz1 h2391 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e305_pos (not_le.mp h2389).le h2388 (not_le.mp h2391).le hz2 hz
        · -- right
          by_cases h2392 : a ≤ ((459171/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2393 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e306_pos (not_le.mp h2388).le h2392 hz1 h2393 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e308_pos (not_le.mp h2388).le h2392 (not_le.mp h2393).le hz2 hz
          · -- right
            by_cases h2394 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e307_pos (not_le.mp h2392).le h2387 hz1 h2394 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e309_pos (not_le.mp h2392).le h2387 (not_le.mp h2394).le hz2 hz
      · -- right
        by_cases h2395 : a ≤ ((230859/1024000 : ℚ) : ℝ)
        · -- left
          by_cases h2396 : a ≤ ((460869/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2397 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e310_pos (not_le.mp h2387).le h2396 hz1 h2397 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e312_pos (not_le.mp h2387).le h2396 (not_le.mp h2397).le hz2 hz
          · -- right
            by_cases h2398 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e311_pos (not_le.mp h2396).le h2395 hz1 h2398 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e313_pos (not_le.mp h2396).le h2395 (not_le.mp h2398).le hz2 hz
        · -- right
          by_cases h2399 : a ≤ ((462567/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2400 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e314_pos (not_le.mp h2395).le h2399 hz1 h2400 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e316_pos (not_le.mp h2395).le h2399 (not_le.mp h2400).le hz2 hz
          · -- right
            by_cases h2401 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e315_pos (not_le.mp h2399).le h2386 hz1 h2401 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e317_pos (not_le.mp h2399).le h2386 (not_le.mp h2401).le hz2 hz
    · -- right
      by_cases h2402 : a ≤ ((116703/512000 : ℚ) : ℝ)
      · -- left
        by_cases h2403 : a ≤ ((232557/1024000 : ℚ) : ℝ)
        · -- left
          by_cases h2404 : a ≤ ((92853/409600 : ℚ) : ℝ)
          · -- left
            by_cases h2405 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e318_pos (not_le.mp h2386).le h2404 hz1 h2405 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e320_pos (not_le.mp h2386).le h2404 (not_le.mp h2405).le hz2 hz
          · -- right
            by_cases h2406 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e319_pos (not_le.mp h2404).le h2403 hz1 h2406 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e321_pos (not_le.mp h2404).le h2403 (not_le.mp h2406).le hz2 hz
        · -- right
          by_cases h2407 : a ≤ ((465963/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2408 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e322_pos (not_le.mp h2403).le h2407 hz1 h2408 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e324_pos (not_le.mp h2403).le h2407 (not_le.mp h2408).le hz2 hz
          · -- right
            by_cases h2409 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e323_pos (not_le.mp h2407).le h2402 hz1 h2409 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e325_pos (not_le.mp h2407).le h2402 (not_le.mp h2409).le hz2 hz
      · -- right
        by_cases h2410 : a ≤ ((46851/204800 : ℚ) : ℝ)
        · -- left
          by_cases h2411 : a ≤ ((467661/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2412 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e326_pos (not_le.mp h2402).le h2411 hz1 h2412 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e328_pos (not_le.mp h2402).le h2411 (not_le.mp h2412).le hz2 hz
          · -- right
            by_cases h2413 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e327_pos (not_le.mp h2411).le h2410 hz1 h2413 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e329_pos (not_le.mp h2411).le h2410 (not_le.mp h2413).le hz2 hz
        · -- right
          by_cases h2414 : a ≤ ((469359/2048000 : ℚ) : ℝ)
          · -- left
            by_cases h2415 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e330_pos (not_le.mp h2410).le h2414 hz1 h2415 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e332_pos (not_le.mp h2410).le h2414 (not_le.mp h2415).le hz2 hz
          · -- right
            by_cases h2416 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B005.e331_pos (not_le.mp h2414).le h2124 hz1 h2416 hz
            · -- right
              exact CKLaneC2R.EpCells.B005.e333_pos (not_le.mp h2414).le h2124 (not_le.mp h2416).le hz2 hz

end CKLaneC2R.EndpointCover


