-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g26
-- name    : CK_CKLaneC2R_CompactCover_S00_g26
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T04:05:49.846928+00:00
-- url     : https://prove2.me/theorems/0c925fec-f19f-4883-9b7a-569aed4f8b9f
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B021

namespace CKLaneC2R.CompactCover

theorem strip0_s031 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : a ≤ ((51/320 : ℚ) : ℝ)) (h254 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h319 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h320 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h321 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h322 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        by_cases h323 : z ≤ ((35633/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B017.c353_pos (not_le.mp h2).le h253 (not_le.mp h254).le h323
        · -- right
          exact CKLaneC2R.Cells.S00.B017.c354_pos (not_le.mp h2).le h253 (not_le.mp h323).le h322
      · -- right
        by_cases h324 : z ≤ ((37459/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B017.c357_pos (not_le.mp h2).le h253 (not_le.mp h322).le h324
        · -- right
          exact CKLaneC2R.Cells.S00.B017.c358_pos (not_le.mp h2).le h253 (not_le.mp h324).le h321
    · -- right
      by_cases h325 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        by_cases h326 : z ≤ ((7857/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B018.c369_pos (not_le.mp h2).le h253 (not_le.mp h321).le h326
        · -- right
          exact CKLaneC2R.Cells.S00.B018.c370_pos (not_le.mp h2).le h253 (not_le.mp h326).le h325
      · -- right
        by_cases h327 : z ≤ ((41111/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B018.c373_pos (not_le.mp h2).le h253 (not_le.mp h325).le h327
        · -- right
          exact CKLaneC2R.Cells.S00.B018.c374_pos (not_le.mp h2).le h253 (not_le.mp h327).le h320
  · -- right
    by_cases h328 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h329 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        by_cases h330 : z ≤ ((42937/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B020.c417_pos (not_le.mp h2).le h253 (not_le.mp h320).le h330
        · -- right
          exact CKLaneC2R.Cells.S00.B020.c418_pos (not_le.mp h2).le h253 (not_le.mp h330).le h329
      · -- right
        by_cases h331 : z ≤ ((44763/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B021.c421_pos (not_le.mp h2).le h253 (not_le.mp h329).le h331
        · -- right
          exact CKLaneC2R.Cells.S00.B021.c422_pos (not_le.mp h2).le h253 (not_le.mp h331).le h328
    · -- right
      by_cases h332 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h333 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B021.c433_pos (not_le.mp h2).le h253 (not_le.mp h328).le h333
        · -- right
          exact CKLaneC2R.Cells.S00.B021.c434_pos (not_le.mp h2).le h253 (not_le.mp h333).le h332
      · -- right
        by_cases h334 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B021.c437_pos (not_le.mp h2).le h253 (not_le.mp h332).le h334
        · -- right
          exact CKLaneC2R.Cells.S00.B021.c438_pos (not_le.mp h2).le h253 (not_le.mp h334).le h319

end CKLaneC2R.CompactCover


