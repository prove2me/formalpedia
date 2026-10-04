-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g44
-- name    : CK_CKLaneC2R_CompactCover_S00_g44
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T23:48:14.258006+00:00
-- url     : https://prove2.me/theorems/3d794793-3a9d-4b8e-bbdd-faaa323774e9
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B048
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B050

namespace CKLaneC2R.CompactCover

theorem strip0_s051 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : a ≤ ((53/320 : ℚ) : ℝ)) (h483 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h542 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h558 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h559 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h560 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h561 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B026.c533_pos (not_le.mp h1).le h482 (not_le.mp h542).le h561
      · -- right
        exact CKLaneC2R.Cells.S00.B026.c534_pos (not_le.mp h1).le h482 (not_le.mp h561).le h560
    · -- right
      by_cases h562 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B026.c537_pos (not_le.mp h1).le h482 (not_le.mp h560).le h562
      · -- right
        exact CKLaneC2R.Cells.S00.B026.c538_pos (not_le.mp h1).le h482 (not_le.mp h562).le h559
  · -- right
    by_cases h563 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h564 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B028.c561_pos (not_le.mp h1).le h482 (not_le.mp h559).le h564
      · -- right
        exact CKLaneC2R.Cells.S00.B028.c562_pos (not_le.mp h1).le h482 (not_le.mp h564).le h563
    · -- right
      by_cases h565 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B028.c569_pos (not_le.mp h1).le h482 (not_le.mp h563).le h565
      · -- right
        exact CKLaneC2R.Cells.S00.B028.c571_pos (not_le.mp h1).le h482 (not_le.mp h565).le h558

theorem strip0_s052 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : a ≤ ((53/320 : ℚ) : ℝ)) (h483 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h542 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h558 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h566 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h567 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h568 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B031.c639_pos (not_le.mp h1).le h482 (not_le.mp h558).le h568
    · -- right
      by_cases h569 : z ≤ ((116003/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B048.c961_pos (not_le.mp h1).le h482 (not_le.mp h568).le h569
      · -- right
        exact CKLaneC2R.Cells.S00.B048.c962_pos (not_le.mp h1).le h482 (not_le.mp h569).le h567
  · -- right
    by_cases h570 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h571 : z ≤ ((117829/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B048.c965_pos (not_le.mp h1).le h482 (not_le.mp h567).le h571
      · -- right
        exact CKLaneC2R.Cells.S00.B048.c966_pos (not_le.mp h1).le h482 (not_le.mp h571).le h570
    · -- right
      by_cases h572 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B048.c969_pos (not_le.mp h1).le h482 (not_le.mp h570).le h572
      · -- right
        exact CKLaneC2R.Cells.S00.B048.c970_pos (not_le.mp h1).le h482 (not_le.mp h572).le h566

theorem strip0_s053 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : a ≤ ((53/320 : ℚ) : ℝ)) (h483 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h542 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h558 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h566 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h573 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h574 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h575 : z ≤ ((121481/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B050.c1006_pos (not_le.mp h1).le h482 (not_le.mp h566).le h575
    · -- right
      exact CKLaneC2R.Cells.S00.B050.c1008_pos (not_le.mp h1).le h482 (not_le.mp h575).le h574
  · -- right
    by_cases h576 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B050.c1014_pos (not_le.mp h1).le h482 (not_le.mp h574).le h576
    · -- right
      exact CKLaneC2R.Cells.S00.B050.c1016_pos (not_le.mp h1).le h482 (not_le.mp h576).le h573

end CKLaneC2R.CompactCover


