-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g53
-- name    : CK_CKLaneC2R_CompactCover_S00_g53
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T01:12:10.799986+00:00
-- url     : https://prove2.me/theorems/f4028bd1-739c-414b-88a7-685bd981c2f2
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B059
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B060

namespace CKLaneC2R.CompactCover

theorem strip0_s064 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : a ≤ ((11/64 : ℚ) : ℝ)) (h694 : z ≤ ((217/400 : ℚ) : ℝ)) (h695 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h696 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h697 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h698 : a ≤ ((109/640 : ℚ) : ℝ)
  · -- left
    by_cases h699 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h700 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h701 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B058.c1163_pos (not_le.mp h481).le h698 hz1 h701
        · -- right
          exact CKLaneC2R.Cells.S00.B058.c1165_pos (not_le.mp h481).le h698 (not_le.mp h701).le h700
      · -- right
        by_cases h702 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B058.c1171_pos (not_le.mp h481).le h698 (not_le.mp h700).le h702
        · -- right
          exact CKLaneC2R.Cells.S00.B058.c1173_pos (not_le.mp h481).le h698 (not_le.mp h702).le h699
    · -- right
      by_cases h703 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h704 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B059.c1195_pos (not_le.mp h481).le h698 (not_le.mp h699).le h704
        · -- right
          exact CKLaneC2R.Cells.S00.B059.c1197_pos (not_le.mp h481).le h698 (not_le.mp h704).le h703
      · -- right
        by_cases h705 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B060.c1203_pos (not_le.mp h481).le h698 (not_le.mp h703).le h705
        · -- right
          exact CKLaneC2R.Cells.S00.B060.c1205_pos (not_le.mp h481).le h698 (not_le.mp h705).le h697
  · -- right
    by_cases h706 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h707 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h708 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B058.c1164_pos (not_le.mp h698).le h693 hz1 h708
        · -- right
          exact CKLaneC2R.Cells.S00.B058.c1166_pos (not_le.mp h698).le h693 (not_le.mp h708).le h707
      · -- right
        by_cases h709 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B058.c1172_pos (not_le.mp h698).le h693 (not_le.mp h707).le h709
        · -- right
          exact CKLaneC2R.Cells.S00.B058.c1174_pos (not_le.mp h698).le h693 (not_le.mp h709).le h706
    · -- right
      by_cases h710 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h711 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B059.c1196_pos (not_le.mp h698).le h693 (not_le.mp h706).le h711
        · -- right
          exact CKLaneC2R.Cells.S00.B059.c1198_pos (not_le.mp h698).le h693 (not_le.mp h711).le h710
      · -- right
        by_cases h712 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B060.c1204_pos (not_le.mp h698).le h693 (not_le.mp h710).le h712
        · -- right
          exact CKLaneC2R.Cells.S00.B060.c1206_pos (not_le.mp h698).le h693 (not_le.mp h712).le h697

end CKLaneC2R.CompactCover


