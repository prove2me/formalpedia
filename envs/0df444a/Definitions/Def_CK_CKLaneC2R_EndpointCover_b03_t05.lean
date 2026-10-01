-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b03_t05
-- name    : CK_CKLaneC2R_EndpointCover_b03_t05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:29:31.673884+00:00
-- url     : https://prove2.me/theorems/77454a87-e050-4cf8-ad58-b40379d6e498
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 6 of 6 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 6 of 6 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 6 of 6 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 6 of 6 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 6 of 6 of 3).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B005
import Definitions.Def_CK_CKLaneC2R_EpCells_B006
import Definitions.Def_CK_CKLaneC2R_EpCells_B007
namespace CKLaneC2R.EndpointCover

theorem cover_sub_019 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((3249/16000 : ℚ) : ℝ))) (h2124 : ¬ (a ≤ ((7347/32000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h2417 : a ≤ ((15543/64000 : ℚ) : ℝ)
  · -- left
    by_cases h2418 : a ≤ ((30237/128000 : ℚ) : ℝ)
    · -- left
      by_cases h2419 : a ≤ ((477/2048 : ℚ) : ℝ)
      · -- left
        by_cases h2420 : a ≤ ((118401/512000 : ℚ) : ℝ)
        · -- left
          by_cases h2421 : a ≤ ((235953/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2422 : a ≤ ((471057/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2423 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e334_pos (not_le.mp h2124).le h2422 hz1 h2423 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e336_pos (not_le.mp h2124).le h2422 (not_le.mp h2423).le hz2 hz
            · -- right
              by_cases h2424 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e335_pos (not_le.mp h2422).le h2421 hz1 h2424 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e337_pos (not_le.mp h2422).le h2421 (not_le.mp h2424).le hz2 hz
          · -- right
            by_cases h2425 : a ≤ ((94551/409600 : ℚ) : ℝ)
            · -- left
              by_cases h2426 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e338_pos (not_le.mp h2421).le h2425 hz1 h2426 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e340_pos (not_le.mp h2421).le h2425 (not_le.mp h2426).le hz2 hz
            · -- right
              by_cases h2427 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e339_pos (not_le.mp h2425).le h2420 hz1 h2427 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e341_pos (not_le.mp h2425).le h2420 (not_le.mp h2427).le hz2 hz
        · -- right
          by_cases h2428 : a ≤ ((237651/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2429 : a ≤ ((474453/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2430 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e342_pos (not_le.mp h2420).le h2429 hz1 h2430 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e344_pos (not_le.mp h2420).le h2429 (not_le.mp h2430).le hz2 hz
            · -- right
              by_cases h2431 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e343_pos (not_le.mp h2429).le h2428 hz1 h2431 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e345_pos (not_le.mp h2429).le h2428 (not_le.mp h2431).le hz2 hz
          · -- right
            by_cases h2432 : a ≤ ((476151/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2433 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e346_pos (not_le.mp h2428).le h2432 hz1 h2433 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e348_pos (not_le.mp h2428).le h2432 (not_le.mp h2433).le hz2 hz
            · -- right
              by_cases h2434 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e347_pos (not_le.mp h2432).le h2419 hz1 h2434 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e349_pos (not_le.mp h2432).le h2419 (not_le.mp h2434).le hz2 hz
      · -- right
        by_cases h2435 : a ≤ ((120099/512000 : ℚ) : ℝ)
        · -- left
          by_cases h2436 : a ≤ ((239349/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2437 : a ≤ ((477849/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2438 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e350_pos (not_le.mp h2419).le h2437 hz1 h2438 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e352_pos (not_le.mp h2419).le h2437 (not_le.mp h2438).le hz2 hz
            · -- right
              by_cases h2439 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e351_pos (not_le.mp h2437).le h2436 hz1 h2439 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e353_pos (not_le.mp h2437).le h2436 (not_le.mp h2439).le hz2 hz
          · -- right
            by_cases h2440 : a ≤ ((479547/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2441 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e354_pos (not_le.mp h2436).le h2440 hz1 h2441 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e356_pos (not_le.mp h2436).le h2440 (not_le.mp h2441).le hz2 hz
            · -- right
              by_cases h2442 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e355_pos (not_le.mp h2440).le h2435 hz1 h2442 hz
              · -- right
                exact CKLaneC2R.EpCells.B005.e357_pos (not_le.mp h2440).le h2435 (not_le.mp h2442).le hz2 hz
        · -- right
          by_cases h2443 : a ≤ ((241047/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2444 : a ≤ ((96249/409600 : ℚ) : ℝ)
            · -- left
              by_cases h2445 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e358_pos (not_le.mp h2435).le h2444 hz1 h2445 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e360_pos (not_le.mp h2435).le h2444 (not_le.mp h2445).le hz2 hz
            · -- right
              by_cases h2446 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B005.e359_pos (not_le.mp h2444).le h2443 hz1 h2446 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e361_pos (not_le.mp h2444).le h2443 (not_le.mp h2446).le hz2 hz
          · -- right
            by_cases h2447 : a ≤ ((482943/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2448 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e362_pos (not_le.mp h2443).le h2447 hz1 h2448 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e364_pos (not_le.mp h2443).le h2447 (not_le.mp h2448).le hz2 hz
            · -- right
              by_cases h2449 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e363_pos (not_le.mp h2447).le h2418 hz1 h2449 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e365_pos (not_le.mp h2447).le h2418 (not_le.mp h2449).le hz2 hz
    · -- right
      by_cases h2450 : a ≤ ((61323/256000 : ℚ) : ℝ)
      · -- left
        by_cases h2451 : a ≤ ((121797/512000 : ℚ) : ℝ)
        · -- left
          by_cases h2452 : a ≤ ((48549/204800 : ℚ) : ℝ)
          · -- left
            by_cases h2453 : a ≤ ((484641/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2454 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e366_pos (not_le.mp h2418).le h2453 hz1 h2454 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e368_pos (not_le.mp h2418).le h2453 (not_le.mp h2454).le hz2 hz
            · -- right
              by_cases h2455 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e367_pos (not_le.mp h2453).le h2452 hz1 h2455 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e369_pos (not_le.mp h2453).le h2452 (not_le.mp h2455).le hz2 hz
          · -- right
            by_cases h2456 : a ≤ ((486339/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2457 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e370_pos (not_le.mp h2452).le h2456 hz1 h2457 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e372_pos (not_le.mp h2452).le h2456 (not_le.mp h2457).le hz2 hz
            · -- right
              by_cases h2458 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e371_pos (not_le.mp h2456).le h2451 hz1 h2458 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e373_pos (not_le.mp h2456).le h2451 (not_le.mp h2458).le hz2 hz
        · -- right
          by_cases h2459 : a ≤ ((244443/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2460 : a ≤ ((488037/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2461 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e374_pos (not_le.mp h2451).le h2460 hz1 h2461 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e376_pos (not_le.mp h2451).le h2460 (not_le.mp h2461).le hz2 hz
            · -- right
              by_cases h2462 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e375_pos (not_le.mp h2460).le h2459 hz1 h2462 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e377_pos (not_le.mp h2460).le h2459 (not_le.mp h2462).le hz2 hz
          · -- right
            by_cases h2463 : a ≤ ((97947/409600 : ℚ) : ℝ)
            · -- left
              by_cases h2464 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e378_pos (not_le.mp h2459).le h2463 hz1 h2464 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e380_pos (not_le.mp h2459).le h2463 (not_le.mp h2464).le hz2 hz
            · -- right
              by_cases h2465 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e379_pos (not_le.mp h2463).le h2450 hz1 h2465 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e381_pos (not_le.mp h2463).le h2450 (not_le.mp h2465).le hz2 hz
      · -- right
        by_cases h2466 : a ≤ ((24699/102400 : ℚ) : ℝ)
        · -- left
          by_cases h2467 : a ≤ ((246141/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2468 : a ≤ ((491433/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2469 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e382_pos (not_le.mp h2450).le h2468 hz1 h2469 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e384_pos (not_le.mp h2450).le h2468 (not_le.mp h2469).le hz2 hz
            · -- right
              by_cases h2470 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e383_pos (not_le.mp h2468).le h2467 hz1 h2470 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e385_pos (not_le.mp h2468).le h2467 (not_le.mp h2470).le hz2 hz
          · -- right
            by_cases h2471 : a ≤ ((493131/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2472 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e386_pos (not_le.mp h2467).le h2471 hz1 h2472 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e388_pos (not_le.mp h2467).le h2471 (not_le.mp h2472).le hz2 hz
            · -- right
              by_cases h2473 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e387_pos (not_le.mp h2471).le h2466 hz1 h2473 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e389_pos (not_le.mp h2471).le h2466 (not_le.mp h2473).le hz2 hz
        · -- right
          by_cases h2474 : a ≤ ((247839/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2475 : a ≤ ((494829/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2476 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e390_pos (not_le.mp h2466).le h2475 hz1 h2476 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e392_pos (not_le.mp h2466).le h2475 (not_le.mp h2476).le hz2 hz
            · -- right
              by_cases h2477 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e391_pos (not_le.mp h2475).le h2474 hz1 h2477 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e393_pos (not_le.mp h2475).le h2474 (not_le.mp h2477).le hz2 hz
          · -- right
            by_cases h2478 : a ≤ ((496527/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2479 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e394_pos (not_le.mp h2474).le h2478 hz1 h2479 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e396_pos (not_le.mp h2474).le h2478 (not_le.mp h2479).le hz2 hz
            · -- right
              by_cases h2480 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e395_pos (not_le.mp h2478).le h2417 hz1 h2480 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e397_pos (not_le.mp h2478).le h2417 (not_le.mp h2480).le hz2 hz
  · -- right
    by_cases h2481 : a ≤ ((6387/25600 : ℚ) : ℝ)
    · -- left
      by_cases h2482 : a ≤ ((63021/256000 : ℚ) : ℝ)
      · -- left
        by_cases h2483 : a ≤ ((125193/512000 : ℚ) : ℝ)
        · -- left
          by_cases h2484 : a ≤ ((249537/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2485 : a ≤ ((19929/81920 : ℚ) : ℝ)
            · -- left
              by_cases h2486 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e398_pos (not_le.mp h2417).le h2485 hz1 h2486 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e400_pos (not_le.mp h2417).le h2485 (not_le.mp h2486).le hz2 hz
            · -- right
              by_cases h2487 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e399_pos (not_le.mp h2485).le h2484 hz1 h2487 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e401_pos (not_le.mp h2485).le h2484 (not_le.mp h2487).le hz2 hz
          · -- right
            by_cases h2488 : a ≤ ((499923/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2489 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e402_pos (not_le.mp h2484).le h2488 hz1 h2489 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e404_pos (not_le.mp h2484).le h2488 (not_le.mp h2489).le hz2 hz
            · -- right
              by_cases h2490 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e403_pos (not_le.mp h2488).le h2483 hz1 h2490 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e405_pos (not_le.mp h2488).le h2483 (not_le.mp h2490).le hz2 hz
        · -- right
          by_cases h2491 : a ≤ ((50247/204800 : ℚ) : ℝ)
          · -- left
            by_cases h2492 : a ≤ ((501621/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2493 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e406_pos (not_le.mp h2483).le h2492 hz1 h2493 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e408_pos (not_le.mp h2483).le h2492 (not_le.mp h2493).le hz2 hz
            · -- right
              by_cases h2494 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e407_pos (not_le.mp h2492).le h2491 hz1 h2494 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e409_pos (not_le.mp h2492).le h2491 (not_le.mp h2494).le hz2 hz
          · -- right
            by_cases h2495 : a ≤ ((503319/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2496 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e410_pos (not_le.mp h2491).le h2495 hz1 h2496 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e412_pos (not_le.mp h2491).le h2495 (not_le.mp h2496).le hz2 hz
            · -- right
              by_cases h2497 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e411_pos (not_le.mp h2495).le h2482 hz1 h2497 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e413_pos (not_le.mp h2495).le h2482 (not_le.mp h2497).le hz2 hz
      · -- right
        by_cases h2498 : a ≤ ((126891/512000 : ℚ) : ℝ)
        · -- left
          by_cases h2499 : a ≤ ((252933/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2500 : a ≤ ((505017/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2501 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e414_pos (not_le.mp h2482).le h2500 hz1 h2501 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e416_pos (not_le.mp h2482).le h2500 (not_le.mp h2501).le hz2 hz
            · -- right
              by_cases h2502 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e415_pos (not_le.mp h2500).le h2499 hz1 h2502 hz
              · -- right
                exact CKLaneC2R.EpCells.B006.e417_pos (not_le.mp h2500).le h2499 (not_le.mp h2502).le hz2 hz
          · -- right
            by_cases h2503 : a ≤ ((101343/409600 : ℚ) : ℝ)
            · -- left
              by_cases h2504 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e418_pos (not_le.mp h2499).le h2503 hz1 h2504 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e420_pos (not_le.mp h2499).le h2503 (not_le.mp h2504).le hz2 hz
            · -- right
              by_cases h2505 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B006.e419_pos (not_le.mp h2503).le h2498 hz1 h2505 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e421_pos (not_le.mp h2503).le h2498 (not_le.mp h2505).le hz2 hz
        · -- right
          by_cases h2506 : a ≤ ((254631/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2507 : a ≤ ((508413/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2508 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e422_pos (not_le.mp h2498).le h2507 hz1 h2508 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e424_pos (not_le.mp h2498).le h2507 (not_le.mp h2508).le hz2 hz
            · -- right
              by_cases h2509 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e423_pos (not_le.mp h2507).le h2506 hz1 h2509 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e425_pos (not_le.mp h2507).le h2506 (not_le.mp h2509).le hz2 hz
          · -- right
            by_cases h2510 : a ≤ ((510111/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2511 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e426_pos (not_le.mp h2506).le h2510 hz1 h2511 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e428_pos (not_le.mp h2506).le h2510 (not_le.mp h2511).le hz2 hz
            · -- right
              by_cases h2512 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e427_pos (not_le.mp h2510).le h2481 hz1 h2512 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e429_pos (not_le.mp h2510).le h2481 (not_le.mp h2512).le hz2 hz
    · -- right
      by_cases h2513 : a ≤ ((64719/256000 : ℚ) : ℝ)
      · -- left
        by_cases h2514 : a ≤ ((128589/512000 : ℚ) : ℝ)
        · -- left
          by_cases h2515 : a ≤ ((256329/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2516 : a ≤ ((511809/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2517 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e430_pos (not_le.mp h2481).le h2516 hz1 h2517 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e432_pos (not_le.mp h2481).le h2516 (not_le.mp h2517).le hz2 hz
            · -- right
              by_cases h2518 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e431_pos (not_le.mp h2516).le h2515 hz1 h2518 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e433_pos (not_le.mp h2516).le h2515 (not_le.mp h2518).le hz2 hz
          · -- right
            by_cases h2519 : a ≤ ((513507/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2520 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e434_pos (not_le.mp h2515).le h2519 hz1 h2520 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e436_pos (not_le.mp h2515).le h2519 (not_le.mp h2520).le hz2 hz
            · -- right
              by_cases h2521 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e435_pos (not_le.mp h2519).le h2514 hz1 h2521 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e437_pos (not_le.mp h2519).le h2514 (not_le.mp h2521).le hz2 hz
        · -- right
          by_cases h2522 : a ≤ ((258027/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2523 : a ≤ ((103041/409600 : ℚ) : ℝ)
            · -- left
              by_cases h2524 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e438_pos (not_le.mp h2514).le h2523 hz1 h2524 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e440_pos (not_le.mp h2514).le h2523 (not_le.mp h2524).le hz2 hz
            · -- right
              by_cases h2525 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e439_pos (not_le.mp h2523).le h2522 hz1 h2525 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e441_pos (not_le.mp h2523).le h2522 (not_le.mp h2525).le hz2 hz
          · -- right
            by_cases h2526 : a ≤ ((516903/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2527 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e442_pos (not_le.mp h2522).le h2526 hz1 h2527 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e444_pos (not_le.mp h2522).le h2526 (not_le.mp h2527).le hz2 hz
            · -- right
              by_cases h2528 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e443_pos (not_le.mp h2526).le h2513 hz1 h2528 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e445_pos (not_le.mp h2526).le h2513 (not_le.mp h2528).le hz2 hz
      · -- right
        by_cases h2529 : a ≤ ((130287/512000 : ℚ) : ℝ)
        · -- left
          by_cases h2530 : a ≤ ((10389/40960 : ℚ) : ℝ)
          · -- left
            by_cases h2531 : a ≤ ((518601/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2532 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e446_pos (not_le.mp h2513).le h2531 hz1 h2532 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e448_pos (not_le.mp h2513).le h2531 (not_le.mp h2532).le hz2 hz
            · -- right
              by_cases h2533 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e447_pos (not_le.mp h2531).le h2530 hz1 h2533 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e449_pos (not_le.mp h2531).le h2530 (not_le.mp h2533).le hz2 hz
          · -- right
            by_cases h2534 : a ≤ ((520299/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2535 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e450_pos (not_le.mp h2530).le h2534 hz1 h2535 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e452_pos (not_le.mp h2530).le h2534 (not_le.mp h2535).le hz2 hz
            · -- right
              by_cases h2536 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e451_pos (not_le.mp h2534).le h2529 hz1 h2536 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e453_pos (not_le.mp h2534).le h2529 (not_le.mp h2536).le hz2 hz
        · -- right
          by_cases h2537 : a ≤ ((261423/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h2538 : a ≤ ((521997/2048000 : ℚ) : ℝ)
            · -- left
              by_cases h2539 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e454_pos (not_le.mp h2529).le h2538 hz1 h2539 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e456_pos (not_le.mp h2529).le h2538 (not_le.mp h2539).le hz2 hz
            · -- right
              by_cases h2540 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e455_pos (not_le.mp h2538).le h2537 hz1 h2540 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e457_pos (not_le.mp h2538).le h2537 (not_le.mp h2540).le hz2 hz
          · -- right
            by_cases h2541 : a ≤ ((104739/409600 : ℚ) : ℝ)
            · -- left
              by_cases h2542 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e458_pos (not_le.mp h2537).le h2541 hz1 h2542 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e460_pos (not_le.mp h2537).le h2541 (not_le.mp h2542).le hz2 hz
            · -- right
              by_cases h2543 : z ≤ ((1999/2000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B007.e459_pos (not_le.mp h2541).le h2 hz1 h2543 hz
              · -- right
                exact CKLaneC2R.EpCells.B007.e461_pos (not_le.mp h2541).le h2 (not_le.mp h2543).le hz2 hz

end CKLaneC2R.EndpointCover


