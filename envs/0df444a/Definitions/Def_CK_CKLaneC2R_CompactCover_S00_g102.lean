-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g102
-- name    : CK_CKLaneC2R_CompactCover_S00_g102
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T01:15:16.782685+00:00
-- url     : https://prove2.me/theorems/5ea4bd10-c7a4-4d39-bee9-08a58a849f4a
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B013

namespace CKLaneC2R.CompactCover

theorem strip0_s129 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) (h1381 : z ≤ ((217/400 : ℚ) : ℝ)) (h1382 : a ≤ ((63/320 : ℚ) : ℝ)) (h1383 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1384 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1400 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h1401 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1402 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B012.c241_pos (not_le.mp h1238).le h1382 (not_le.mp h1384).le h1402
      · -- right
        exact CKLaneC2R.Cells.S00.B012.c242_pos (not_le.mp h1238).le h1382 (not_le.mp h1402).le h1401
    · -- right
      by_cases h1403 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B012.c245_pos (not_le.mp h1238).le h1382 (not_le.mp h1401).le h1403
      · -- right
        exact CKLaneC2R.Cells.S00.B012.c246_pos (not_le.mp h1238).le h1382 (not_le.mp h1403).le h1400
  · -- right
    by_cases h1404 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1405 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B012.c257_pos (not_le.mp h1238).le h1382 (not_le.mp h1400).le h1405
      · -- right
        exact CKLaneC2R.Cells.S00.B012.c258_pos (not_le.mp h1238).le h1382 (not_le.mp h1405).le h1404
    · -- right
      by_cases h1406 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B013.c261_pos (not_le.mp h1238).le h1382 (not_le.mp h1404).le h1406
      · -- right
        exact CKLaneC2R.Cells.S00.B013.c262_pos (not_le.mp h1238).le h1382 (not_le.mp h1406).le h1383

end CKLaneC2R.CompactCover


