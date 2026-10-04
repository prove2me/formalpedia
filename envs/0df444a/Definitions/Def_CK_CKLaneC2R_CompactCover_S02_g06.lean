-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g06
-- name    : CK_CKLaneC2R_CompactCover_S02_g06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T21:06:09.528316+00:00
-- url     : https://prove2.me/theorems/89135213-d5bd-482b-b484-1fbede978c00
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B038
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B015

namespace CKLaneC2R.CompactCover

theorem strip2_s008 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((5/16 : ℚ) : ℝ))) (h93 : z ≤ ((217/400 : ℚ) : ℝ)) (h94 : a ≤ ((51/160 : ℚ) : ℝ)) (h95 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h96 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h97 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h98 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h99 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h100 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B038.c763_pos (not_le.mp h3).le h94 hz1 h100
          · -- right
            exact CKLaneC2R.Cells.S02.B038.c764_pos (not_le.mp h3).le h94 (not_le.mp h100).le h99
        · -- right
          by_cases h101 : z ≤ ((13747/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B038.c767_pos (not_le.mp h3).le h94 (not_le.mp h99).le h101
          · -- right
            exact CKLaneC2R.Cells.S02.B038.c768_pos (not_le.mp h3).le h94 (not_le.mp h101).le h98
      · -- right
        by_cases h102 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B029.c583_pos (not_le.mp h3).le h94 (not_le.mp h98).le h102
        · -- right
          exact CKLaneC2R.Cells.S02.B029.c585_pos (not_le.mp h3).le h94 (not_le.mp h102).le h97
    · -- right
      by_cases h103 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h104 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B029.c595_pos (not_le.mp h3).le h94 (not_le.mp h97).le h104
        · -- right
          exact CKLaneC2R.Cells.S02.B029.c596_pos (not_le.mp h3).le h94 (not_le.mp h104).le h103
      · -- right
        by_cases h105 : z ≤ ((2379/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B029.c599_pos (not_le.mp h3).le h94 (not_le.mp h103).le h105
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c600_pos (not_le.mp h3).le h94 (not_le.mp h105).le h96
  · -- right
    by_cases h106 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h107 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h108 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B031.c633_pos (not_le.mp h3).le h94 (not_le.mp h96).le h108
        · -- right
          exact CKLaneC2R.Cells.S02.B031.c634_pos (not_le.mp h3).le h94 (not_le.mp h108).le h107
      · -- right
        exact CKLaneC2R.Cells.S02.B014.c294_pos (not_le.mp h3).le h94 (not_le.mp h107).le h106
    · -- right
      by_cases h109 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B015.c300_pos (not_le.mp h3).le h94 (not_le.mp h106).le h109
      · -- right
        exact CKLaneC2R.Cells.S02.B015.c302_pos (not_le.mp h3).le h94 (not_le.mp h109).le h95

end CKLaneC2R.CompactCover


