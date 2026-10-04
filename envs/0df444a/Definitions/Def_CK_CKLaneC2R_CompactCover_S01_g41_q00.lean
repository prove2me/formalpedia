-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g41_q00
-- name    : CK_CKLaneC2R_CompactCover_S01_g41_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T01:54:53.298559+00:00
-- url     : https://prove2.me/theorems/ad3de15a-37c4-48d6-8a1a-b97dd4486b42
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B051
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B037
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B038
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B009


namespace CKLaneC2R.CompactCover

theorem strip1_s052 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : ¬ (a ≤ ((37/160 : ℚ) : ℝ))) (h513 : z ≤ ((217/400 : ℚ) : ℝ)) (h514 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h515 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h516 : a ≤ ((15/64 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h517 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h518 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h519 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h520 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B051.c1022_pos (not_le.mp h420).le h516 hz1 h520
        · -- right
          exact CKLaneC2R.Cells.S01.B051.c1024_pos (not_le.mp h420).le h516 (not_le.mp h520).le h519
      · -- right
        by_cases h521 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B051.c1026_pos (not_le.mp h420).le h516 (not_le.mp h519).le h521
        · -- right
          exact CKLaneC2R.Cells.S01.B051.c1027_pos (not_le.mp h420).le h516 (not_le.mp h521).le h518
    · -- right
      by_cases h522 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h523 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B051.c1034_pos (not_le.mp h420).le h516 (not_le.mp h518).le h523
        · -- right
          exact CKLaneC2R.Cells.S01.B051.c1035_pos (not_le.mp h420).le h516 (not_le.mp h523).le h522
      · -- right
        exact CKLaneC2R.Cells.S01.B036.c724_pos (not_le.mp h420).le h516 (not_le.mp h522).le h517
  · -- right
    by_cases h524 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h525 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B036.c738_pos (not_le.mp h420).le h516 (not_le.mp h517).le h525
      · -- right
        exact CKLaneC2R.Cells.S01.B037.c740_pos (not_le.mp h420).le h516 (not_le.mp h525).le h524
    · -- right
      by_cases h526 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B037.c746_pos (not_le.mp h420).le h516 (not_le.mp h524).le h526
      · -- right
        exact CKLaneC2R.Cells.S01.B037.c748_pos (not_le.mp h420).le h516 (not_le.mp h526).le h515

end CKLaneC2R.CompactCover


