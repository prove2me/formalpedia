-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g04
-- name    : CK_CKLaneC2R_CompactCover_S05_g04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T00:47:31.447728+00:00
-- url     : https://prove2.me/theorems/829e8698-90cd-4850-b0c1-3393ca813688
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B023

namespace CKLaneC2R.CompactCover

theorem strip5_s007 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : a ≤ ((3699/4000 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((7299/8000 : ℚ) : ℝ))) (h34 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h43 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h48 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h52 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h56 : a ≤ ((14697/16000 : ℚ) : ℝ)
  · -- left
    by_cases h57 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h58 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B012.c255_pos (not_le.mp h2).le h56 (not_le.mp h52).le h58
      · -- right
        exact CKLaneC2R.Cells.S05.B012.c257_pos (not_le.mp h2).le h56 (not_le.mp h58).le h57
    · -- right
      by_cases h59 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B013.c269_pos (not_le.mp h2).le h56 (not_le.mp h57).le h59
      · -- right
        by_cases h60 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B016.c336_pos (not_le.mp h2).le h56 (not_le.mp h59).le h60
        · -- right
          by_cases h61 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B020.c401_pos (not_le.mp h2).le h56 (not_le.mp h60).le h61
          · -- right
            by_cases h62 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B023.c465_pos (not_le.mp h2).le h56 (not_le.mp h61).le h62
            · -- right
              exact CKLaneC2R.Cells.S05.B023.c467_pos (not_le.mp h2).le h56 (not_le.mp h62).le hz2
  · -- right
    by_cases h63 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h64 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B012.c256_pos (not_le.mp h56).le h1 (not_le.mp h52).le h64
      · -- right
        exact CKLaneC2R.Cells.S05.B012.c258_pos (not_le.mp h56).le h1 (not_le.mp h64).le h63
    · -- right
      by_cases h65 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B013.c270_pos (not_le.mp h56).le h1 (not_le.mp h63).le h65
      · -- right
        by_cases h66 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B016.c337_pos (not_le.mp h56).le h1 (not_le.mp h65).le h66
        · -- right
          by_cases h67 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B020.c402_pos (not_le.mp h56).le h1 (not_le.mp h66).le h67
          · -- right
            by_cases h68 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B023.c466_pos (not_le.mp h56).le h1 (not_le.mp h67).le h68
            · -- right
              exact CKLaneC2R.Cells.S05.B023.c468_pos (not_le.mp h56).le h1 (not_le.mp h68).le hz2

end CKLaneC2R.CompactCover


