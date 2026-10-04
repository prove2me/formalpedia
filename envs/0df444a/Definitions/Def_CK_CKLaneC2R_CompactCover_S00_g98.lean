-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g98
-- name    : CK_CKLaneC2R_CompactCover_S00_g98
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T11:53:10.774075+00:00
-- url     : https://prove2.me/theorems/da940a5d-f593-4c5f-9bb6-b3aa8a2667c5
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B030

namespace CKLaneC2R.CompactCover

theorem strip0_s123 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1314 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1331 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1332 : a ≤ ((61/320 : ℚ) : ℝ)
  · -- left
    by_cases h1333 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h1334 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1335 : z ≤ ((50241/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B029.c593_pos (not_le.mp h891).le h1332 (not_le.mp h1314).le h1335
        · -- right
          exact CKLaneC2R.Cells.S00.B029.c594_pos (not_le.mp h891).le h1332 (not_le.mp h1335).le h1334
      · -- right
        by_cases h1336 : z ≤ ((52067/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B029.c597_pos (not_le.mp h891).le h1332 (not_le.mp h1334).le h1336
        · -- right
          exact CKLaneC2R.Cells.S00.B029.c599_pos (not_le.mp h891).le h1332 (not_le.mp h1336).le h1333
    · -- right
      by_cases h1337 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1338 : z ≤ ((53893/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B031.c623_pos (not_le.mp h891).le h1332 (not_le.mp h1333).le h1338
        · -- right
          exact CKLaneC2R.Cells.S00.B031.c625_pos (not_le.mp h891).le h1332 (not_le.mp h1338).le h1337
      · -- right
        by_cases h1339 : z ≤ ((55719/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B031.c631_pos (not_le.mp h891).le h1332 (not_le.mp h1337).le h1339
        · -- right
          exact CKLaneC2R.Cells.S00.B031.c633_pos (not_le.mp h891).le h1332 (not_le.mp h1339).le h1331
  · -- right
    by_cases h1340 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h1341 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1342 : z ≤ ((50241/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B029.c595_pos (not_le.mp h1332).le h1238 (not_le.mp h1314).le h1342
        · -- right
          exact CKLaneC2R.Cells.S00.B029.c596_pos (not_le.mp h1332).le h1238 (not_le.mp h1342).le h1341
      · -- right
        by_cases h1343 : z ≤ ((52067/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B029.c598_pos (not_le.mp h1332).le h1238 (not_le.mp h1341).le h1343
        · -- right
          exact CKLaneC2R.Cells.S00.B030.c600_pos (not_le.mp h1332).le h1238 (not_le.mp h1343).le h1340
    · -- right
      by_cases h1344 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1345 : z ≤ ((53893/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B031.c624_pos (not_le.mp h1332).le h1238 (not_le.mp h1340).le h1345
        · -- right
          exact CKLaneC2R.Cells.S00.B031.c626_pos (not_le.mp h1332).le h1238 (not_le.mp h1345).le h1344
      · -- right
        by_cases h1346 : z ≤ ((55719/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B031.c632_pos (not_le.mp h1332).le h1238 (not_le.mp h1344).le h1346
        · -- right
          exact CKLaneC2R.Cells.S00.B031.c634_pos (not_le.mp h1332).le h1238 (not_le.mp h1346).le h1331

end CKLaneC2R.CompactCover


