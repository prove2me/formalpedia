-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g25
-- name    : CK_CKLaneC2R_CompactCover_S00_g25
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T12:35:44.33545+00:00
-- url     : https://prove2.me/theorems/bef4b8e4-4d02-40cb-9ee5-559afe0ecde2
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B006

namespace CKLaneC2R.CompactCover

theorem strip0_s030 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : a ≤ ((51/320 : ℚ) : ℝ)) (h254 : z ≤ ((217/400 : ℚ) : ℝ)) (h255 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h303 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h304 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h305 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h306 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          by_cases h307 : a ≤ ((101/640 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B041.c823_pos (not_le.mp h2).le h307 (not_le.mp h255).le h306
          · -- right
            exact CKLaneC2R.Cells.S00.B041.c824_pos (not_le.mp h307).le h253 (not_le.mp h255).le h306
        · -- right
          exact CKLaneC2R.Cells.S00.B004.c82_pos (not_le.mp h2).le h253 (not_le.mp h306).le h305
      · -- right
        by_cases h308 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B004.c85_pos (not_le.mp h2).le h253 (not_le.mp h305).le h308
        · -- right
          exact CKLaneC2R.Cells.S00.B004.c86_pos (not_le.mp h2).le h253 (not_le.mp h308).le h304
    · -- right
      by_cases h309 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h310 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B004.c95_pos (not_le.mp h2).le h253 (not_le.mp h304).le h310
        · -- right
          exact CKLaneC2R.Cells.S00.B004.c96_pos (not_le.mp h2).le h253 (not_le.mp h310).le h309
      · -- right
        by_cases h311 : z ≤ ((26503/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B004.c99_pos (not_le.mp h2).le h253 (not_le.mp h309).le h311
        · -- right
          exact CKLaneC2R.Cells.S00.B005.c100_pos (not_le.mp h2).le h253 (not_le.mp h311).le h303
  · -- right
    by_cases h312 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h313 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        by_cases h314 : z ≤ ((28329/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B005.c111_pos (not_le.mp h2).le h253 (not_le.mp h303).le h314
        · -- right
          exact CKLaneC2R.Cells.S00.B005.c112_pos (not_le.mp h2).le h253 (not_le.mp h314).le h313
      · -- right
        by_cases h315 : z ≤ ((6031/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B005.c115_pos (not_le.mp h2).le h253 (not_le.mp h313).le h315
        · -- right
          exact CKLaneC2R.Cells.S00.B005.c116_pos (not_le.mp h2).le h253 (not_le.mp h315).le h312
    · -- right
      by_cases h316 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        by_cases h317 : z ≤ ((31981/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B006.c127_pos (not_le.mp h2).le h253 (not_le.mp h312).le h317
        · -- right
          exact CKLaneC2R.Cells.S00.B006.c128_pos (not_le.mp h2).le h253 (not_le.mp h317).le h316
      · -- right
        by_cases h318 : z ≤ ((33807/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B006.c131_pos (not_le.mp h2).le h253 (not_le.mp h316).le h318
        · -- right
          exact CKLaneC2R.Cells.S00.B006.c132_pos (not_le.mp h2).le h253 (not_le.mp h318).le h254

end CKLaneC2R.CompactCover


