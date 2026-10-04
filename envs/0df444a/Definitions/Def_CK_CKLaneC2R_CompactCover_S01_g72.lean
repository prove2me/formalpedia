-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g72
-- name    : CK_CKLaneC2R_CompactCover_S01_g72
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T14:28:59.549742+00:00
-- url     : https://prove2.me/theorems/bba0b8af-c64e-4915-829e-7b31479331b1
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B042
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B000

namespace CKLaneC2R.CompactCover

theorem strip1_s103 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : a ≤ ((23/80 : ℚ) : ℝ)) (h999 : z ≤ ((217/400 : ℚ) : ℝ)) (h1000 : a ≤ ((9/32 : ℚ) : ℝ)) (h1001 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1002 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1003 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h1004 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h1005 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1006 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B041.c824_pos (not_le.mp h746).le h1000 hz1 h1006
        · -- right
          exact CKLaneC2R.Cells.S01.B041.c825_pos (not_le.mp h746).le h1000 (not_le.mp h1006).le h1005
      · -- right
        by_cases h1007 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B041.c828_pos (not_le.mp h746).le h1000 (not_le.mp h1005).le h1007
        · -- right
          exact CKLaneC2R.Cells.S01.B041.c829_pos (not_le.mp h746).le h1000 (not_le.mp h1007).le h1004
    · -- right
      by_cases h1008 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1009 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B042.c840_pos (not_le.mp h746).le h1000 (not_le.mp h1004).le h1009
        · -- right
          exact CKLaneC2R.Cells.S01.B042.c841_pos (not_le.mp h746).le h1000 (not_le.mp h1009).le h1008
      · -- right
        by_cases h1010 : a ≤ ((89/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B042.c842_pos (not_le.mp h746).le h1010 (not_le.mp h1008).le h1003
        · -- right
          exact CKLaneC2R.Cells.S01.B042.c843_pos (not_le.mp h1010).le h1000 (not_le.mp h1008).le h1003
  · -- right
    by_cases h1011 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1012 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B016.c332_pos (not_le.mp h746).le h1000 (not_le.mp h1003).le h1012
      · -- right
        exact CKLaneC2R.Cells.S01.B016.c333_pos (not_le.mp h746).le h1000 (not_le.mp h1012).le h1011
    · -- right
      by_cases h1013 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B016.c336_pos (not_le.mp h746).le h1000 (not_le.mp h1011).le h1013
      · -- right
        exact CKLaneC2R.Cells.S01.B016.c337_pos (not_le.mp h746).le h1000 (not_le.mp h1013).le h1002

theorem strip1_s104 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : a ≤ ((23/80 : ℚ) : ℝ)) (h999 : z ≤ ((217/400 : ℚ) : ℝ)) (h1000 : a ≤ ((9/32 : ℚ) : ℝ)) (h1001 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1002 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1014 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h1015 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1016 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B019.c380_pos (not_le.mp h746).le h1000 (not_le.mp h1002).le h1016
      · -- right
        exact CKLaneC2R.Cells.S01.B019.c381_pos (not_le.mp h746).le h1000 (not_le.mp h1016).le h1015
    · -- right
      by_cases h1017 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B019.c384_pos (not_le.mp h746).le h1000 (not_le.mp h1015).le h1017
      · -- right
        exact CKLaneC2R.Cells.S01.B019.c385_pos (not_le.mp h746).le h1000 (not_le.mp h1017).le h1014
  · -- right
    by_cases h1018 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1019 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B019.c396_pos (not_le.mp h746).le h1000 (not_le.mp h1014).le h1019
      · -- right
        exact CKLaneC2R.Cells.S01.B019.c397_pos (not_le.mp h746).le h1000 (not_le.mp h1019).le h1018
    · -- right
      exact CKLaneC2R.Cells.S01.B000.c6_pos (not_le.mp h746).le h1000 (not_le.mp h1018).le h1001

end CKLaneC2R.CompactCover


