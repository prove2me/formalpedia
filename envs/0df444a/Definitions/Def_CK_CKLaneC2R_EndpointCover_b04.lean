-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b04
-- name    : CK_CKLaneC2R_EndpointCover_b04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:41:56.637663+00:00
-- url     : https://prove2.me/theorems/8ec07c2c-ce03-4d7e-8ca7-b92e4b5681e8
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 5 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 5 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 5 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 5 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 5 of 5).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B001
import Definitions.Def_CK_CKLaneC2R_EpCells_B002
import Definitions.Def_CK_CKLaneC2R_EpCells_B003__2
import Definitions.Def_CK_CKLaneC2R_EpCells_B007
import Definitions.Def_CK_CKLaneC2R_EpCells_B008
namespace CKLaneC2R.EndpointCover

theorem cover_sub_020 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((2049/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h2544 : a ≤ ((4947/16000 : ℚ) : ℝ)
  · -- left
    by_cases h2545 : a ≤ ((1809/6400 : ℚ) : ℝ)
    · -- left
      by_cases h2546 : a ≤ ((17241/64000 : ℚ) : ℝ)
      · -- left
        by_cases h2547 : a ≤ ((33633/128000 : ℚ) : ℝ)
        · -- left
          by_cases h2548 : a ≤ ((66417/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2549 : a ≤ ((26397/102400 : ℚ) : ℝ)
            · -- left
              by_cases h2550 : a ≤ ((263121/1024000 : ℚ) : ℝ)
              · -- left
                by_cases h2551 : a ≤ ((525393/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2552 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B007.e462_pos (not_le.mp h2).le h2551 hz1 h2552 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B007.e464_pos (not_le.mp h2).le h2551 (not_le.mp h2552).le hz2 hz
                · -- right
                  by_cases h2553 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B007.e463_pos (not_le.mp h2551).le h2550 hz1 h2553 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B007.e465_pos (not_le.mp h2551).le h2550 (not_le.mp h2553).le hz2 hz
              · -- right
                by_cases h2554 : a ≤ ((527091/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2555 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B007.e466_pos (not_le.mp h2550).le h2554 hz1 h2555 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B007.e468_pos (not_le.mp h2550).le h2554 (not_le.mp h2555).le hz2 hz
                · -- right
                  by_cases h2556 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B007.e467_pos (not_le.mp h2554).le h2549 hz1 h2556 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B007.e469_pos (not_le.mp h2554).le h2549 (not_le.mp h2556).le hz2 hz
            · -- right
              by_cases h2557 : a ≤ ((264819/1024000 : ℚ) : ℝ)
              · -- left
                by_cases h2558 : a ≤ ((528789/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2559 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B007.e470_pos (not_le.mp h2549).le h2558 hz1 h2559 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B007.e472_pos (not_le.mp h2549).le h2558 (not_le.mp h2559).le hz2 hz
                · -- right
                  by_cases h2560 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B007.e471_pos (not_le.mp h2558).le h2557 hz1 h2560 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B007.e473_pos (not_le.mp h2558).le h2557 (not_le.mp h2560).le hz2 hz
              · -- right
                by_cases h2561 : a ≤ ((530487/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2562 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B007.e474_pos (not_le.mp h2557).le h2561 hz1 h2562 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B007.e476_pos (not_le.mp h2557).le h2561 (not_le.mp h2562).le hz2 hz
                · -- right
                  by_cases h2563 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B007.e475_pos (not_le.mp h2561).le h2548 hz1 h2563 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B007.e477_pos (not_le.mp h2561).le h2548 (not_le.mp h2563).le hz2 hz
          · -- right
            by_cases h2564 : a ≤ ((133683/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2565 : a ≤ ((266517/1024000 : ℚ) : ℝ)
              · -- left
                by_cases h2566 : a ≤ ((106437/409600 : ℚ) : ℝ)
                · -- left
                  by_cases h2567 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B007.e478_pos (not_le.mp h2548).le h2566 hz1 h2567 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e480_pos (not_le.mp h2548).le h2566 (not_le.mp h2567).le hz2 hz
                · -- right
                  by_cases h2568 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B007.e479_pos (not_le.mp h2566).le h2565 hz1 h2568 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e481_pos (not_le.mp h2566).le h2565 (not_le.mp h2568).le hz2 hz
              · -- right
                by_cases h2569 : a ≤ ((533883/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2570 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e482_pos (not_le.mp h2565).le h2569 hz1 h2570 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e484_pos (not_le.mp h2565).le h2569 (not_le.mp h2570).le hz2 hz
                · -- right
                  by_cases h2571 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e483_pos (not_le.mp h2569).le h2564 hz1 h2571 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e485_pos (not_le.mp h2569).le h2564 (not_le.mp h2571).le hz2 hz
            · -- right
              by_cases h2572 : a ≤ ((53643/204800 : ℚ) : ℝ)
              · -- left
                by_cases h2573 : a ≤ ((535581/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2574 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e486_pos (not_le.mp h2564).le h2573 hz1 h2574 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e488_pos (not_le.mp h2564).le h2573 (not_le.mp h2574).le hz2 hz
                · -- right
                  by_cases h2575 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e487_pos (not_le.mp h2573).le h2572 hz1 h2575 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e489_pos (not_le.mp h2573).le h2572 (not_le.mp h2575).le hz2 hz
              · -- right
                by_cases h2576 : a ≤ ((537279/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2577 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e490_pos (not_le.mp h2572).le h2576 hz1 h2577 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e492_pos (not_le.mp h2572).le h2576 (not_le.mp h2577).le hz2 hz
                · -- right
                  by_cases h2578 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e491_pos (not_le.mp h2576).le h2547 hz1 h2578 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e493_pos (not_le.mp h2576).le h2547 (not_le.mp h2578).le hz2 hz
        · -- right
          by_cases h2579 : a ≤ ((13623/51200 : ℚ) : ℝ)
          · -- left
            by_cases h2580 : a ≤ ((135381/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2581 : a ≤ ((269913/1024000 : ℚ) : ℝ)
              · -- left
                by_cases h2582 : a ≤ ((538977/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2583 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e494_pos (not_le.mp h2547).le h2582 hz1 h2583 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e496_pos (not_le.mp h2547).le h2582 (not_le.mp h2583).le hz2 hz
                · -- right
                  by_cases h2584 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e495_pos (not_le.mp h2582).le h2581 hz1 h2584 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e497_pos (not_le.mp h2582).le h2581 (not_le.mp h2584).le hz2 hz
              · -- right
                by_cases h2585 : a ≤ ((21627/81920 : ℚ) : ℝ)
                · -- left
                  by_cases h2586 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e498_pos (not_le.mp h2581).le h2585 hz1 h2586 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e500_pos (not_le.mp h2581).le h2585 (not_le.mp h2586).le hz2 hz
                · -- right
                  by_cases h2587 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e499_pos (not_le.mp h2585).le h2580 hz1 h2587 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e501_pos (not_le.mp h2585).le h2580 (not_le.mp h2587).le hz2 hz
            · -- right
              by_cases h2588 : a ≤ ((271611/1024000 : ℚ) : ℝ)
              · -- left
                by_cases h2589 : a ≤ ((542373/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2590 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e502_pos (not_le.mp h2580).le h2589 hz1 h2590 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e504_pos (not_le.mp h2580).le h2589 (not_le.mp h2590).le hz2 hz
                · -- right
                  by_cases h2591 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e503_pos (not_le.mp h2589).le h2588 hz1 h2591 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e505_pos (not_le.mp h2589).le h2588 (not_le.mp h2591).le hz2 hz
              · -- right
                by_cases h2592 : a ≤ ((544071/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2593 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e506_pos (not_le.mp h2588).le h2592 hz1 h2593 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e508_pos (not_le.mp h2588).le h2592 (not_le.mp h2593).le hz2 hz
                · -- right
                  by_cases h2594 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e507_pos (not_le.mp h2592).le h2579 hz1 h2594 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e509_pos (not_le.mp h2592).le h2579 (not_le.mp h2594).le hz2 hz
          · -- right
            by_cases h2595 : a ≤ ((137079/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2596 : a ≤ ((273309/1024000 : ℚ) : ℝ)
              · -- left
                by_cases h2597 : a ≤ ((545769/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2598 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e510_pos (not_le.mp h2579).le h2597 hz1 h2598 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e512_pos (not_le.mp h2579).le h2597 (not_le.mp h2598).le hz2 hz
                · -- right
                  by_cases h2599 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e511_pos (not_le.mp h2597).le h2596 hz1 h2599 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e513_pos (not_le.mp h2597).le h2596 (not_le.mp h2599).le hz2 hz
              · -- right
                by_cases h2600 : a ≤ ((547467/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2601 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e514_pos (not_le.mp h2596).le h2600 hz1 h2601 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e516_pos (not_le.mp h2596).le h2600 (not_le.mp h2601).le hz2 hz
                · -- right
                  by_cases h2602 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e515_pos (not_le.mp h2600).le h2595 hz1 h2602 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e517_pos (not_le.mp h2600).le h2595 (not_le.mp h2602).le hz2 hz
            · -- right
              by_cases h2603 : a ≤ ((275007/1024000 : ℚ) : ℝ)
              · -- left
                by_cases h2604 : a ≤ ((109833/409600 : ℚ) : ℝ)
                · -- left
                  by_cases h2605 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e518_pos (not_le.mp h2595).le h2604 hz1 h2605 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e520_pos (not_le.mp h2595).le h2604 (not_le.mp h2605).le hz2 hz
                · -- right
                  by_cases h2606 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e519_pos (not_le.mp h2604).le h2603 hz1 h2606 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e521_pos (not_le.mp h2604).le h2603 (not_le.mp h2606).le hz2 hz
              · -- right
                by_cases h2607 : a ≤ ((550863/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2608 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e522_pos (not_le.mp h2603).le h2607 hz1 h2608 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e524_pos (not_le.mp h2603).le h2607 (not_le.mp h2608).le hz2 hz
                · -- right
                  by_cases h2609 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e523_pos (not_le.mp h2607).le h2546 hz1 h2609 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e525_pos (not_le.mp h2607).le h2546 (not_le.mp h2609).le hz2 hz
      · -- right
        by_cases h2610 : a ≤ ((35331/128000 : ℚ) : ℝ)
        · -- left
          by_cases h2611 : a ≤ ((69813/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2612 : a ≤ ((138777/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2613 : a ≤ ((55341/204800 : ℚ) : ℝ)
              · -- left
                by_cases h2614 : a ≤ ((552561/2048000 : ℚ) : ℝ)
                · -- left
                  by_cases h2615 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e526_pos (not_le.mp h2546).le h2614 hz1 h2615 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e528_pos (not_le.mp h2546).le h2614 (not_le.mp h2615).le hz2 hz
                · -- right
                  by_cases h2616 : z ≤ ((1999/2000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e527_pos (not_le.mp h2614).le h2613 hz1 h2616 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e529_pos (not_le.mp h2614).le h2613 (not_le.mp h2616).le hz2 hz
              · -- right
                by_cases h2617 : z ≤ ((1999/2000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B004.e255_pos (not_le.mp h2613).le h2612 hz1 h2617 hz
                · -- right
                  by_cases h2618 : a ≤ ((554259/2048000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B008.e530_pos (not_le.mp h2613).le h2618 (not_le.mp h2617).le hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B008.e531_pos (not_le.mp h2618).le h2612 (not_le.mp h2617).le hz2 hz
            · -- right
              by_cases h2619 : a ≤ ((278403/1024000 : ℚ) : ℝ)
              · -- left
                by_cases h2620 : z ≤ ((1999/2000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B004.e256_pos (not_le.mp h2612).le h2619 hz1 h2620 hz
                · -- right
                  exact CKLaneC2R.EpCells.B004.e257_pos (not_le.mp h2612).le h2619 (not_le.mp h2620).le hz2 hz
              · -- right
                by_cases h2621 : z ≤ ((1999/2000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B004.e258_pos (not_le.mp h2619).le h2611 hz1 h2621 hz
                · -- right
                  exact CKLaneC2R.EpCells.B004.e259_pos (not_le.mp h2619).le h2611 (not_le.mp h2621).le hz2 hz
          · -- right
            by_cases h2622 : a ≤ ((5619/20480 : ℚ) : ℝ)
            · -- left
              by_cases h2623 : a ≤ ((280101/1024000 : ℚ) : ℝ)
              · -- left
                by_cases h2624 : z ≤ ((1999/2000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B004.e260_pos (not_le.mp h2611).le h2623 hz1 h2624 hz
                · -- right
                  exact CKLaneC2R.EpCells.B004.e261_pos (not_le.mp h2611).le h2623 (not_le.mp h2624).le hz2 hz
              · -- right
                by_cases h2625 : z ≤ ((1999/2000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B004.e262_pos (not_le.mp h2623).le h2622 hz1 h2625 hz
                · -- right
                  exact CKLaneC2R.EpCells.B004.e263_pos (not_le.mp h2623).le h2622 (not_le.mp h2625).le hz2 hz
            · -- right
              by_cases h2626 : a ≤ ((281799/1024000 : ℚ) : ℝ)
              · -- left
                by_cases h2627 : z ≤ ((1999/2000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B004.e264_pos (not_le.mp h2622).le h2626 hz1 h2627 hz
                · -- right
                  exact CKLaneC2R.EpCells.B004.e265_pos (not_le.mp h2622).le h2626 (not_le.mp h2627).le hz2 hz
              · -- right
                by_cases h2628 : z ≤ ((1999/2000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B004.e266_pos (not_le.mp h2626).le h2610 hz1 h2628 hz
                · -- right
                  exact CKLaneC2R.EpCells.B004.e267_pos (not_le.mp h2626).le h2610 (not_le.mp h2628).le hz2 hz
        · -- right
          by_cases h2629 : a ≤ ((71511/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2630 : a ≤ ((142173/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2631 : a ≤ ((283497/1024000 : ℚ) : ℝ)
              · -- left
                by_cases h2632 : z ≤ ((1999/2000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B004.e268_pos (not_le.mp h2610).le h2631 hz1 h2632 hz
                · -- right
                  exact CKLaneC2R.EpCells.B004.e269_pos (not_le.mp h2610).le h2631 (not_le.mp h2632).le hz2 hz
              · -- right
                by_cases h2633 : z ≤ ((1999/2000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B004.e270_pos (not_le.mp h2631).le h2630 hz1 h2633 hz
                · -- right
                  exact CKLaneC2R.EpCells.B004.e271_pos (not_le.mp h2631).le h2630 (not_le.mp h2633).le hz2 hz
            · -- right
              by_cases h2634 : a ≤ ((57039/204800 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e167_pos (not_le.mp h2630).le h2634 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e168_pos (not_le.mp h2634).le h2629 hz1 hz2 hz
          · -- right
            by_cases h2635 : a ≤ ((143871/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2636 : a ≤ ((286893/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e169_pos (not_le.mp h2629).le h2636 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e170_pos (not_le.mp h2636).le h2635 hz1 hz2 hz
            · -- right
              by_cases h2637 : a ≤ ((288591/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e171_pos (not_le.mp h2635).le h2637 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e172_pos (not_le.mp h2637).le h2545 hz1 hz2 hz
    · -- right
      by_cases h2638 : a ≤ ((18939/64000 : ℚ) : ℝ)
      · -- left
        by_cases h2639 : a ≤ ((37029/128000 : ℚ) : ℝ)
        · -- left
          by_cases h2640 : a ≤ ((73209/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2641 : a ≤ ((145569/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2642 : a ≤ ((290289/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e173_pos (not_le.mp h2545).le h2642 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e174_pos (not_le.mp h2642).le h2641 hz1 hz2 hz
            · -- right
              by_cases h2643 : a ≤ ((291987/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e175_pos (not_le.mp h2641).le h2643 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e176_pos (not_le.mp h2643).le h2640 hz1 hz2 hz
          · -- right
            by_cases h2644 : a ≤ ((147267/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2645 : a ≤ ((58737/204800 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e177_pos (not_le.mp h2640).le h2645 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e178_pos (not_le.mp h2645).le h2644 hz1 hz2 hz
            · -- right
              by_cases h2646 : a ≤ ((295383/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e179_pos (not_le.mp h2644).le h2646 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e180_pos (not_le.mp h2646).le h2639 hz1 hz2 hz
        · -- right
          by_cases h2647 : a ≤ ((74907/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2648 : a ≤ ((29793/102400 : ℚ) : ℝ)
            · -- left
              by_cases h2649 : a ≤ ((297081/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e181_pos (not_le.mp h2639).le h2649 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e182_pos (not_le.mp h2649).le h2648 hz1 hz2 hz
            · -- right
              by_cases h2650 : a ≤ ((298779/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e183_pos (not_le.mp h2648).le h2650 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e184_pos (not_le.mp h2650).le h2647 hz1 hz2 hz
          · -- right
            by_cases h2651 : a ≤ ((150663/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2652 : a ≤ ((300477/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e185_pos (not_le.mp h2647).le h2652 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e186_pos (not_le.mp h2652).le h2651 hz1 hz2 hz
            · -- right
              by_cases h2653 : a ≤ ((12087/40960 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e187_pos (not_le.mp h2651).le h2653 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e188_pos (not_le.mp h2653).le h2638 hz1 hz2 hz
      · -- right
        by_cases h2654 : a ≤ ((38727/128000 : ℚ) : ℝ)
        · -- left
          by_cases h2655 : a ≤ ((15321/51200 : ℚ) : ℝ)
          · -- left
            by_cases h2656 : a ≤ ((152361/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2657 : a ≤ ((303873/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e189_pos (not_le.mp h2638).le h2657 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e190_pos (not_le.mp h2657).le h2656 hz1 hz2 hz
            · -- right
              by_cases h2658 : a ≤ ((305571/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e191_pos (not_le.mp h2656).le h2658 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e192_pos (not_le.mp h2658).le h2655 hz1 hz2 hz
          · -- right
            by_cases h2659 : a ≤ ((154059/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2660 : a ≤ ((307269/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e193_pos (not_le.mp h2655).le h2660 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e194_pos (not_le.mp h2660).le h2659 hz1 hz2 hz
            · -- right
              by_cases h2661 : a ≤ ((308967/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e195_pos (not_le.mp h2659).le h2661 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e196_pos (not_le.mp h2661).le h2654 hz1 hz2 hz
        · -- right
          by_cases h2662 : a ≤ ((78303/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2663 : a ≤ ((155757/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2664 : a ≤ ((62133/204800 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e197_pos (not_le.mp h2654).le h2664 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e198_pos (not_le.mp h2664).le h2663 hz1 hz2 hz
            · -- right
              by_cases h2665 : a ≤ ((312363/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e199_pos (not_le.mp h2663).le h2665 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e200_pos (not_le.mp h2665).le h2662 hz1 hz2 hz
          · -- right
            by_cases h2666 : a ≤ ((31491/102400 : ℚ) : ℝ)
            · -- left
              by_cases h2667 : a ≤ ((314061/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e201_pos (not_le.mp h2662).le h2667 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e202_pos (not_le.mp h2667).le h2666 hz1 hz2 hz
            · -- right
              by_cases h2668 : a ≤ ((315759/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e203_pos (not_le.mp h2666).le h2668 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e204_pos (not_le.mp h2668).le h2544 hz1 hz2 hz
  · -- right
    by_cases h2669 : a ≤ ((10743/32000 : ℚ) : ℝ)
    · -- left
      by_cases h2670 : a ≤ ((20637/64000 : ℚ) : ℝ)
      · -- left
        by_cases h2671 : a ≤ ((1617/5120 : ℚ) : ℝ)
        · -- left
          by_cases h2672 : a ≤ ((80001/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2673 : a ≤ ((159153/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2674 : a ≤ ((317457/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e205_pos (not_le.mp h2544).le h2674 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e206_pos (not_le.mp h2674).le h2673 hz1 hz2 hz
            · -- right
              by_cases h2675 : a ≤ ((63831/204800 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e207_pos (not_le.mp h2673).le h2675 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e208_pos (not_le.mp h2675).le h2672 hz1 hz2 hz
          · -- right
            by_cases h2676 : a ≤ ((160851/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2677 : a ≤ ((320853/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e209_pos (not_le.mp h2672).le h2677 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e210_pos (not_le.mp h2677).le h2676 hz1 hz2 hz
            · -- right
              by_cases h2678 : a ≤ ((322551/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e211_pos (not_le.mp h2676).le h2678 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e212_pos (not_le.mp h2678).le h2671 hz1 hz2 hz
        · -- right
          by_cases h2679 : a ≤ ((81699/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2680 : a ≤ ((162549/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2681 : a ≤ ((324249/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e213_pos (not_le.mp h2671).le h2681 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e214_pos (not_le.mp h2681).le h2680 hz1 hz2 hz
            · -- right
              by_cases h2682 : a ≤ ((325947/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e215_pos (not_le.mp h2680).le h2682 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e216_pos (not_le.mp h2682).le h2679 hz1 hz2 hz
          · -- right
            by_cases h2683 : a ≤ ((164247/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2684 : a ≤ ((65529/204800 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e217_pos (not_le.mp h2679).le h2684 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e218_pos (not_le.mp h2684).le h2683 hz1 hz2 hz
            · -- right
              by_cases h2685 : a ≤ ((329343/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e219_pos (not_le.mp h2683).le h2685 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e220_pos (not_le.mp h2685).le h2670 hz1 hz2 hz
      · -- right
        by_cases h2686 : a ≤ ((42123/128000 : ℚ) : ℝ)
        · -- left
          by_cases h2687 : a ≤ ((83397/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2688 : a ≤ ((33189/102400 : ℚ) : ℝ)
            · -- left
              by_cases h2689 : a ≤ ((331041/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e221_pos (not_le.mp h2670).le h2689 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e222_pos (not_le.mp h2689).le h2688 hz1 hz2 hz
            · -- right
              by_cases h2690 : a ≤ ((332739/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e223_pos (not_le.mp h2688).le h2690 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e224_pos (not_le.mp h2690).le h2687 hz1 hz2 hz
          · -- right
            by_cases h2691 : a ≤ ((167643/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2692 : a ≤ ((334437/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e225_pos (not_le.mp h2687).le h2692 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e226_pos (not_le.mp h2692).le h2691 hz1 hz2 hz
            · -- right
              by_cases h2693 : a ≤ ((67227/204800 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e227_pos (not_le.mp h2691).le h2693 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e228_pos (not_le.mp h2693).le h2686 hz1 hz2 hz
        · -- right
          by_cases h2694 : a ≤ ((17019/51200 : ℚ) : ℝ)
          · -- left
            by_cases h2695 : a ≤ ((169341/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2696 : a ≤ ((337833/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e229_pos (not_le.mp h2686).le h2696 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e230_pos (not_le.mp h2696).le h2695 hz1 hz2 hz
            · -- right
              by_cases h2697 : a ≤ ((339531/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e231_pos (not_le.mp h2695).le h2697 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e232_pos (not_le.mp h2697).le h2694 hz1 hz2 hz
          · -- right
            by_cases h2698 : a ≤ ((171039/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2699 : a ≤ ((341229/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e233_pos (not_le.mp h2694).le h2699 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e234_pos (not_le.mp h2699).le h2698 hz1 hz2 hz
            · -- right
              by_cases h2700 : a ≤ ((342927/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e235_pos (not_le.mp h2698).le h2700 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e236_pos (not_le.mp h2700).le h2669 hz1 hz2 hz
    · -- right
      by_cases h2701 : a ≤ ((4467/12800 : ℚ) : ℝ)
      · -- left
        by_cases h2702 : a ≤ ((43821/128000 : ℚ) : ℝ)
        · -- left
          by_cases h2703 : a ≤ ((86793/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2704 : a ≤ ((172737/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2705 : a ≤ ((2757/8192 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e237_pos (not_le.mp h2669).le h2705 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B003.e238_pos (not_le.mp h2705).le h2704 hz1 hz2 hz
            · -- right
              by_cases h2706 : a ≤ ((346323/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B003.e239_pos (not_le.mp h2704).le h2706 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B004.e240_pos (not_le.mp h2706).le h2703 hz1 hz2 hz
          · -- right
            by_cases h2707 : a ≤ ((34887/102400 : ℚ) : ℝ)
            · -- left
              by_cases h2708 : a ≤ ((348021/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B004.e241_pos (not_le.mp h2703).le h2708 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B004.e242_pos (not_le.mp h2708).le h2707 hz1 hz2 hz
            · -- right
              by_cases h2709 : a ≤ ((349719/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B004.e243_pos (not_le.mp h2707).le h2709 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B004.e244_pos (not_le.mp h2709).le h2702 hz1 hz2 hz
        · -- right
          by_cases h2710 : a ≤ ((88491/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2711 : a ≤ ((176133/512000 : ℚ) : ℝ)
            · -- left
              by_cases h2712 : a ≤ ((351417/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B004.e245_pos (not_le.mp h2702).le h2712 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B004.e246_pos (not_le.mp h2712).le h2711 hz1 hz2 hz
            · -- right
              by_cases h2713 : a ≤ ((70623/204800 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B004.e247_pos (not_le.mp h2711).le h2713 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B004.e248_pos (not_le.mp h2713).le h2710 hz1 hz2 hz
          · -- right
            by_cases h2714 : a ≤ ((177831/512000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e105_pos (not_le.mp h2710).le h2714 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e106_pos (not_le.mp h2714).le h2701 hz1 hz2 hz
      · -- right
        by_cases h2715 : a ≤ ((45519/128000 : ℚ) : ℝ)
        · -- left
          by_cases h2716 : a ≤ ((90189/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2717 : a ≤ ((179529/512000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e107_pos (not_le.mp h2701).le h2717 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e108_pos (not_le.mp h2717).le h2716 hz1 hz2 hz
          · -- right
            by_cases h2718 : a ≤ ((181227/512000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e109_pos (not_le.mp h2716).le h2718 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e110_pos (not_le.mp h2718).le h2715 hz1 hz2 hz
        · -- right
          by_cases h2719 : a ≤ ((91887/256000 : ℚ) : ℝ)
          · -- left
            by_cases h2720 : a ≤ ((7317/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e111_pos (not_le.mp h2715).le h2720 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e112_pos (not_le.mp h2720).le h2719 hz1 hz2 hz
          · -- right
            by_cases h2721 : a ≤ ((184623/512000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e113_pos (not_le.mp h2719).le h2721 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e114_pos (not_le.mp h2721).le h1 hz1 hz2 hz

end CKLaneC2R.EndpointCover


