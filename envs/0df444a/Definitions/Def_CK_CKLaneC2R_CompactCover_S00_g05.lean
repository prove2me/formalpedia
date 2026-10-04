-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g05
-- name    : CK_CKLaneC2R_CompactCover_S00_g05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T11:15:04.563595+00:00
-- url     : https://prove2.me/theorems/0ddc4542-b16e-4170-bfbe-0c731fd2e21e
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B006

namespace CKLaneC2R.CompactCover

theorem strip0_s006 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) (h57 : z ≤ ((3427/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h58 : z ≤ ((5941/16000 : ℚ) : ℝ)
  · -- left
    by_cases h59 : a ≤ ((97/640 : ℚ) : ℝ)
    · -- left
      by_cases h60 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h61 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B040.c809_pos ha1 h59 (not_le.mp h5).le h61
        · -- right
          exact CKLaneC2R.Cells.S00.B040.c811_pos ha1 h59 (not_le.mp h61).le h60
      · -- right
        by_cases h62 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B040.c817_pos ha1 h59 (not_le.mp h60).le h62
        · -- right
          exact CKLaneC2R.Cells.S00.B040.c819_pos ha1 h59 (not_le.mp h62).le h58
    · -- right
      by_cases h63 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h64 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B040.c810_pos (not_le.mp h59).le h3 (not_le.mp h5).le h64
        · -- right
          exact CKLaneC2R.Cells.S00.B040.c812_pos (not_le.mp h59).le h3 (not_le.mp h64).le h63
      · -- right
        by_cases h65 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B040.c818_pos (not_le.mp h59).le h3 (not_le.mp h63).le h65
        · -- right
          exact CKLaneC2R.Cells.S00.B041.c820_pos (not_le.mp h59).le h3 (not_le.mp h65).le h58
  · -- right
    by_cases h66 : z ≤ ((2559/6400 : ℚ) : ℝ)
    · -- left
      by_cases h67 : a ≤ ((97/640 : ℚ) : ℝ)
      · -- left
        by_cases h68 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B041.c825_pos ha1 h67 (not_le.mp h58).le h68
        · -- right
          exact CKLaneC2R.Cells.S00.B041.c827_pos ha1 h67 (not_le.mp h68).le h66
      · -- right
        by_cases h69 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B041.c826_pos (not_le.mp h67).le h3 (not_le.mp h58).le h69
        · -- right
          exact CKLaneC2R.Cells.S00.B041.c828_pos (not_le.mp h67).le h3 (not_le.mp h69).le h66
    · -- right
      by_cases h70 : z ≤ ((26503/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B004.c91_pos ha1 h3 (not_le.mp h66).le h70
      · -- right
        exact CKLaneC2R.Cells.S00.B004.c92_pos ha1 h3 (not_le.mp h70).le h57

theorem strip0_s007 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) (h57 : ¬ (z ≤ ((3427/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h71 : z ≤ ((7767/16000 : ℚ) : ℝ)
  · -- left
    by_cases h72 : z ≤ ((14621/32000 : ℚ) : ℝ)
    · -- left
      by_cases h73 : z ≤ ((28329/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B005.c103_pos ha1 h3 (not_le.mp h57).le h73
      · -- right
        exact CKLaneC2R.Cells.S00.B005.c104_pos ha1 h3 (not_le.mp h73).le h72
    · -- right
      by_cases h74 : z ≤ ((6031/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B005.c107_pos ha1 h3 (not_le.mp h72).le h74
      · -- right
        exact CKLaneC2R.Cells.S00.B005.c108_pos ha1 h3 (not_le.mp h74).le h71
  · -- right
    by_cases h75 : z ≤ ((16447/32000 : ℚ) : ℝ)
    · -- left
      by_cases h76 : z ≤ ((31981/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B005.c119_pos ha1 h3 (not_le.mp h71).le h76
      · -- right
        exact CKLaneC2R.Cells.S00.B006.c120_pos ha1 h3 (not_le.mp h76).le h75
    · -- right
      by_cases h77 : z ≤ ((33807/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B006.c123_pos ha1 h3 (not_le.mp h75).le h77
      · -- right
        exact CKLaneC2R.Cells.S00.B006.c124_pos ha1 h3 (not_le.mp h77).le h4

end CKLaneC2R.CompactCover


