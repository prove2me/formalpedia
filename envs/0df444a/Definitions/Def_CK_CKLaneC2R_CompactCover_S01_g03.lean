-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g03
-- name    : CK_CKLaneC2R_CompactCover_S01_g03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T22:55:25.930982+00:00
-- url     : https://prove2.me/theorems/408af5b8-e0c2-49dc-9747-13a619ba72b3
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B047
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B048
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B050
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B032

namespace CKLaneC2R.CompactCover

theorem strip1_s003 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : a ≤ ((33/160 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : ¬ (a ≤ ((13/64 : ℚ) : ℝ))) (h36 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h37 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h38 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h39 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h40 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h41 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          by_cases h42 : a ≤ ((131/640 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B056.c1131_pos (not_le.mp h5).le h42 hz1 h41
          · -- right
            exact CKLaneC2R.Cells.S01.B056.c1132_pos (not_le.mp h42).le h3 hz1 h41
        · -- right
          exact CKLaneC2R.Cells.S01.B047.c951_pos (not_le.mp h5).le h3 (not_le.mp h41).le h40
      · -- right
        by_cases h43 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B047.c954_pos (not_le.mp h5).le h3 (not_le.mp h40).le h43
        · -- right
          exact CKLaneC2R.Cells.S01.B047.c955_pos (not_le.mp h5).le h3 (not_le.mp h43).le h39
    · -- right
      by_cases h44 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h45 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B048.c966_pos (not_le.mp h5).le h3 (not_le.mp h39).le h45
        · -- right
          exact CKLaneC2R.Cells.S01.B048.c967_pos (not_le.mp h5).le h3 (not_le.mp h45).le h44
      · -- right
        by_cases h46 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B048.c970_pos (not_le.mp h5).le h3 (not_le.mp h44).le h46
        · -- right
          exact CKLaneC2R.Cells.S01.B048.c971_pos (not_le.mp h5).le h3 (not_le.mp h46).le h38
  · -- right
    by_cases h47 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h48 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h49 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B050.c1010_pos (not_le.mp h5).le h3 (not_le.mp h38).le h49
        · -- right
          exact CKLaneC2R.Cells.S01.B050.c1011_pos (not_le.mp h5).le h3 (not_le.mp h49).le h48
      · -- right
        exact CKLaneC2R.Cells.S01.B031.c635_pos (not_le.mp h5).le h3 (not_le.mp h48).le h47
    · -- right
      by_cases h50 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B032.c640_pos (not_le.mp h5).le h3 (not_le.mp h47).le h50
      · -- right
        exact CKLaneC2R.Cells.S01.B032.c642_pos (not_le.mp h5).le h3 (not_le.mp h50).le h37

end CKLaneC2R.CompactCover


