-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g35
-- name    : CK_CKLaneC2R_CompactCover_S02_g35
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T02:43:11.293308+00:00
-- url     : https://prove2.me/theorems/540fb671-b91e-4bef-85b5-f0e7d7c14813
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B010

namespace CKLaneC2R.CompactCover

theorem strip2_s053 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : a ≤ ((17/40 : ℚ) : ℝ)) (h536 : a ≤ ((33/80 : ℚ) : ℝ)) (h537 : z ≤ ((217/400 : ℚ) : ℝ)) (h538 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h554 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h555 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h556 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B005.c100_pos (not_le.mp h0).le h536 (not_le.mp h538).le h556
      · -- right
        exact CKLaneC2R.Cells.S02.B005.c101_pos (not_le.mp h0).le h536 (not_le.mp h556).le h555
    · -- right
      by_cases h557 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B005.c104_pos (not_le.mp h0).le h536 (not_le.mp h555).le h557
      · -- right
        exact CKLaneC2R.Cells.S02.B005.c105_pos (not_le.mp h0).le h536 (not_le.mp h557).le h554
  · -- right
    by_cases h558 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h559 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B005.c116_pos (not_le.mp h0).le h536 (not_le.mp h554).le h559
      · -- right
        exact CKLaneC2R.Cells.S02.B005.c117_pos (not_le.mp h0).le h536 (not_le.mp h559).le h558
    · -- right
      by_cases h560 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B006.c120_pos (not_le.mp h0).le h536 (not_le.mp h558).le h560
      · -- right
        exact CKLaneC2R.Cells.S02.B006.c121_pos (not_le.mp h0).le h536 (not_le.mp h560).le h537

theorem strip2_s054 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : a ≤ ((17/40 : ℚ) : ℝ)) (h536 : a ≤ ((33/80 : ℚ) : ℝ)) (h537 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h561 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h562 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h563 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h564 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B009.c194_pos (not_le.mp h0).le h536 (not_le.mp h537).le h564
      · -- right
        exact CKLaneC2R.Cells.S02.B009.c195_pos (not_le.mp h0).le h536 (not_le.mp h564).le h563
    · -- right
      by_cases h565 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B009.c198_pos (not_le.mp h0).le h536 (not_le.mp h563).le h565
      · -- right
        exact CKLaneC2R.Cells.S02.B009.c199_pos (not_le.mp h0).le h536 (not_le.mp h565).le h562
  · -- right
    by_cases h566 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h567 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B010.c208_pos (not_le.mp h0).le h536 (not_le.mp h562).le h567
      · -- right
        exact CKLaneC2R.Cells.S02.B010.c209_pos (not_le.mp h0).le h536 (not_le.mp h567).le h566
    · -- right
      by_cases h568 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B010.c212_pos (not_le.mp h0).le h536 (not_le.mp h566).le h568
      · -- right
        exact CKLaneC2R.Cells.S02.B010.c213_pos (not_le.mp h0).le h536 (not_le.mp h568).le h561

end CKLaneC2R.CompactCover


