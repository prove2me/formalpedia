-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g46
-- name    : CK_CKLaneC2R_CompactCover_S01_g46
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T22:25:44.725991+00:00
-- url     : https://prove2.me/theorems/9bb7ce19-bd47-494b-80db-40276c5e9f11
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B051
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B052
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B037
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B038

namespace CKLaneC2R.CompactCover

theorem strip1_s060 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : a ≤ ((39/160 : ℚ) : ℝ)) (h599 : z ≤ ((217/400 : ℚ) : ℝ)) (h600 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h601 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h602 : a ≤ ((77/320 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h603 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h604 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h605 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h606 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B051.c1036_pos (not_le.mp h419).le h602 hz1 h606
        · -- right
          exact CKLaneC2R.Cells.S01.B051.c1038_pos (not_le.mp h419).le h602 (not_le.mp h606).le h605
      · -- right
        by_cases h607 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B052.c1044_pos (not_le.mp h419).le h602 (not_le.mp h605).le h607
        · -- right
          exact CKLaneC2R.Cells.S01.B052.c1045_pos (not_le.mp h419).le h602 (not_le.mp h607).le h604
    · -- right
      by_cases h608 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B036.c726_pos (not_le.mp h419).le h602 (not_le.mp h604).le h608
      · -- right
        exact CKLaneC2R.Cells.S01.B036.c728_pos (not_le.mp h419).le h602 (not_le.mp h608).le h603
  · -- right
    by_cases h609 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h610 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B037.c750_pos (not_le.mp h419).le h602 (not_le.mp h603).le h610
      · -- right
        exact CKLaneC2R.Cells.S01.B037.c752_pos (not_le.mp h419).le h602 (not_le.mp h610).le h609
    · -- right
      by_cases h611 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B037.c758_pos (not_le.mp h419).le h602 (not_le.mp h609).le h611
      · -- right
        exact CKLaneC2R.Cells.S01.B038.c760_pos (not_le.mp h419).le h602 (not_le.mp h611).le h601

theorem strip1_s061 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : a ≤ ((39/160 : ℚ) : ℝ)) (h599 : z ≤ ((217/400 : ℚ) : ℝ)) (h600 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h601 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h602 : ¬ (a ≤ ((77/320 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h612 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h613 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h614 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h615 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B051.c1037_pos (not_le.mp h602).le h598 hz1 h615
        · -- right
          exact CKLaneC2R.Cells.S01.B051.c1039_pos (not_le.mp h602).le h598 (not_le.mp h615).le h614
      · -- right
        by_cases h616 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B052.c1046_pos (not_le.mp h602).le h598 (not_le.mp h614).le h616
        · -- right
          exact CKLaneC2R.Cells.S01.B052.c1047_pos (not_le.mp h602).le h598 (not_le.mp h616).le h613
    · -- right
      by_cases h617 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B036.c727_pos (not_le.mp h602).le h598 (not_le.mp h613).le h617
      · -- right
        exact CKLaneC2R.Cells.S01.B036.c729_pos (not_le.mp h602).le h598 (not_le.mp h617).le h612
  · -- right
    by_cases h618 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h619 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B037.c751_pos (not_le.mp h602).le h598 (not_le.mp h612).le h619
      · -- right
        exact CKLaneC2R.Cells.S01.B037.c753_pos (not_le.mp h602).le h598 (not_le.mp h619).le h618
    · -- right
      by_cases h620 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B037.c759_pos (not_le.mp h602).le h598 (not_le.mp h618).le h620
      · -- right
        exact CKLaneC2R.Cells.S01.B038.c761_pos (not_le.mp h602).le h598 (not_le.mp h620).le h601

end CKLaneC2R.CompactCover


