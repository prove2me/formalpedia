-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g104
-- name    : CK_CKLaneC2R_CompactCover_S00_g104
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T03:10:34.092456+00:00
-- url     : https://prove2.me/theorems/a775d8a6-e828-4815-8136-b819e206fbd3
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B064
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B042
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B043
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B010

namespace CKLaneC2R.CompactCover

theorem strip0_s131 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) (h1381 : z ≤ ((217/400 : ℚ) : ℝ)) (h1382 : ¬ (a ≤ ((63/320 : ℚ) : ℝ))) (h1417 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1418 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1419 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h1420 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h1421 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1422 : a ≤ ((127/640 : ℚ) : ℝ)
        · -- left
          by_cases h1423 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B064.c1285_pos (not_le.mp h1382).le h1422 hz1 h1423
          · -- right
            exact CKLaneC2R.Cells.S00.B064.c1287_pos (not_le.mp h1382).le h1422 (not_le.mp h1423).le h1421
        · -- right
          by_cases h1424 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B064.c1286_pos (not_le.mp h1422).le ha2 hz1 h1424
          · -- right
            exact CKLaneC2R.Cells.S00.B064.c1288_pos (not_le.mp h1422).le ha2 (not_le.mp h1424).le h1421
      · -- right
        by_cases h1425 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B042.c843_pos (not_le.mp h1382).le ha2 (not_le.mp h1421).le h1425
        · -- right
          exact CKLaneC2R.Cells.S00.B042.c844_pos (not_le.mp h1382).le ha2 (not_le.mp h1425).le h1420
    · -- right
      by_cases h1426 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1427 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B042.c855_pos (not_le.mp h1382).le ha2 (not_le.mp h1420).le h1427
        · -- right
          exact CKLaneC2R.Cells.S00.B042.c856_pos (not_le.mp h1382).le ha2 (not_le.mp h1427).le h1426
      · -- right
        by_cases h1428 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B042.c859_pos (not_le.mp h1382).le ha2 (not_le.mp h1426).le h1428
        · -- right
          exact CKLaneC2R.Cells.S00.B043.c860_pos (not_le.mp h1382).le ha2 (not_le.mp h1428).le h1419
  · -- right
    by_cases h1429 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1430 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1431 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B045.c903_pos (not_le.mp h1382).le ha2 (not_le.mp h1419).le h1431
        · -- right
          exact CKLaneC2R.Cells.S00.B045.c904_pos (not_le.mp h1382).le ha2 (not_le.mp h1431).le h1430
      · -- right
        by_cases h1432 : z ≤ ((21051/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B045.c907_pos (not_le.mp h1382).le ha2 (not_le.mp h1430).le h1432
        · -- right
          exact CKLaneC2R.Cells.S00.B045.c908_pos (not_le.mp h1382).le ha2 (not_le.mp h1432).le h1429
    · -- right
      by_cases h1433 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B010.c202_pos (not_le.mp h1382).le ha2 (not_le.mp h1429).le h1433
      · -- right
        exact CKLaneC2R.Cells.S00.B010.c204_pos (not_le.mp h1382).le ha2 (not_le.mp h1433).le h1418

end CKLaneC2R.CompactCover


