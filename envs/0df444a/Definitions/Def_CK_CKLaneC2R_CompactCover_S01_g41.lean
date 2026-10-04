-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g41
-- name    : CK_CKLaneC2R_CompactCover_S01_g41
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T02:31:15.09229+00:00
-- url     : https://prove2.me/theorems/289be835-2d31-40f7-9e10-f7ba87e7c059
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g41_q01

namespace CKLaneC2R.CompactCover
theorem strip1_s054 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : ¬ (a ≤ ((37/160 : ℚ) : ℝ))) (h513 : z ≤ ((217/400 : ℚ) : ℝ)) (h514 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h515 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h536 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h537 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h538 : a ≤ ((15/64 : ℚ) : ℝ)
      · -- left
        by_cases h539 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B038.c770_pos (not_le.mp h420).le h538 (not_le.mp h515).le h539
        · -- right
          exact CKLaneC2R.Cells.S01.B038.c772_pos (not_le.mp h420).le h538 (not_le.mp h539).le h537
      · -- right
        by_cases h540 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B038.c771_pos (not_le.mp h538).le h419 (not_le.mp h515).le h540
        · -- right
          exact CKLaneC2R.Cells.S01.B038.c773_pos (not_le.mp h538).le h419 (not_le.mp h540).le h537
    · -- right
      by_cases h541 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        by_cases h542 : a ≤ ((15/64 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B038.c778_pos (not_le.mp h420).le h542 (not_le.mp h537).le h541
        · -- right
          exact CKLaneC2R.Cells.S01.B038.c779_pos (not_le.mp h542).le h419 (not_le.mp h537).le h541
      · -- right
        exact CKLaneC2R.Cells.S01.B009.c184_pos (not_le.mp h420).le h419 (not_le.mp h541).le h536
  · -- right
    by_cases h543 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h544 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B009.c189_pos (not_le.mp h420).le h419 (not_le.mp h536).le h544
      · -- right
        exact CKLaneC2R.Cells.S01.B009.c190_pos (not_le.mp h420).le h419 (not_le.mp h544).le h543
    · -- right
      by_cases h545 : a ≤ ((15/64 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B009.c191_pos (not_le.mp h420).le h545 (not_le.mp h543).le h514
      · -- right
        exact CKLaneC2R.Cells.S01.B009.c192_pos (not_le.mp h545).le h419 (not_le.mp h543).le h514

end CKLaneC2R.CompactCover


