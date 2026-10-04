-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g28
-- name    : CK_CKLaneC2R_CompactCover_S01_g28
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T20:35:42.632306+00:00
-- url     : https://prove2.me/theorems/c761d9a7-e6e0-4e01-bf91-5b77178c3203
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B049
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B050
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B033

namespace CKLaneC2R.CompactCover

theorem strip1_s035 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : ¬ (a ≤ ((7/32 : ℚ) : ℝ))) (h324 : z ≤ ((217/400 : ℚ) : ℝ)) (h325 : ¬ (a ≤ ((71/320 : ℚ) : ℝ))) (h351 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h352 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h353 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h354 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h355 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h356 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B049.c989_pos (not_le.mp h325).le h1 hz1 h356
        · -- right
          exact CKLaneC2R.Cells.S01.B049.c991_pos (not_le.mp h325).le h1 (not_le.mp h356).le h355
      · -- right
        by_cases h357 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B049.c994_pos (not_le.mp h325).le h1 (not_le.mp h355).le h357
        · -- right
          exact CKLaneC2R.Cells.S01.B049.c995_pos (not_le.mp h325).le h1 (not_le.mp h357).le h354
    · -- right
      by_cases h358 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h359 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B050.c1006_pos (not_le.mp h325).le h1 (not_le.mp h354).le h359
        · -- right
          exact CKLaneC2R.Cells.S01.B050.c1007_pos (not_le.mp h325).le h1 (not_le.mp h359).le h358
      · -- right
        exact CKLaneC2R.Cells.S01.B031.c633_pos (not_le.mp h325).le h1 (not_le.mp h358).le h353
  · -- right
    by_cases h360 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h361 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B032.c652_pos (not_le.mp h325).le h1 (not_le.mp h353).le h361
      · -- right
        exact CKLaneC2R.Cells.S01.B032.c654_pos (not_le.mp h325).le h1 (not_le.mp h361).le h360
    · -- right
      by_cases h362 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B033.c660_pos (not_le.mp h325).le h1 (not_le.mp h360).le h362
      · -- right
        exact CKLaneC2R.Cells.S01.B033.c662_pos (not_le.mp h325).le h1 (not_le.mp h362).le h352

end CKLaneC2R.CompactCover


