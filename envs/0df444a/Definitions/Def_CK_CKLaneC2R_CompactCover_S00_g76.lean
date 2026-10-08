-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g76
-- name    : CK_CKLaneC2R_CompactCover_S00_g76
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T12:59:34.970353+00:00
-- url     : https://prove2.me/theorems/20758905-89e7-479d-927d-98709d7b03ab
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B043
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B044
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B011

namespace CKLaneC2R.CompactCover

theorem strip0_s092 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : ¬ (a ≤ ((57/320 : ℚ) : ℝ))) (h988 : z ≤ ((217/400 : ℚ) : ℝ)) (h989 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h990 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h991 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1005 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h1006 : z ≤ ((10069/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1007 : z ≤ ((769/5120 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B043.c863_pos (not_le.mp h893).le h892 (not_le.mp h991).le h1007
      · -- right
        exact CKLaneC2R.Cells.S00.B043.c864_pos (not_le.mp h893).le h892 (not_le.mp h1007).le h1006
    · -- right
      by_cases h1008 : z ≤ ((21051/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B043.c867_pos (not_le.mp h893).le h892 (not_le.mp h1006).le h1008
      · -- right
        exact CKLaneC2R.Cells.S00.B043.c868_pos (not_le.mp h893).le h892 (not_le.mp h1008).le h1005
  · -- right
    by_cases h1009 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      by_cases h1010 : z ≤ ((22877/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B044.c881_pos (not_le.mp h893).le h892 (not_le.mp h1005).le h1010
      · -- right
        exact CKLaneC2R.Cells.S00.B044.c882_pos (not_le.mp h893).le h892 (not_le.mp h1010).le h1009
    · -- right
      by_cases h1011 : a ≤ ((23/128 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B044.c883_pos (not_le.mp h893).le h1011 (not_le.mp h1009).le h990
      · -- right
        exact CKLaneC2R.Cells.S00.B044.c884_pos (not_le.mp h1011).le h892 (not_le.mp h1009).le h990

theorem strip0_s093 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : ¬ (a ≤ ((57/320 : ℚ) : ℝ))) (h988 : z ≤ ((217/400 : ℚ) : ℝ)) (h989 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h990 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1012 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h1013 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1014 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1015 : a ≤ ((23/128 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B045.c917_pos (not_le.mp h893).le h1015 (not_le.mp h990).le h1014
        · -- right
          exact CKLaneC2R.Cells.S00.B045.c918_pos (not_le.mp h1015).le h892 (not_le.mp h990).le h1014
      · -- right
        exact CKLaneC2R.Cells.S00.B010.c205_pos (not_le.mp h893).le h892 (not_le.mp h1014).le h1013
    · -- right
      by_cases h1016 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B010.c208_pos (not_le.mp h893).le h892 (not_le.mp h1013).le h1016
      · -- right
        exact CKLaneC2R.Cells.S00.B010.c209_pos (not_le.mp h893).le h892 (not_le.mp h1016).le h1012
  · -- right
    by_cases h1017 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1018 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B010.c219_pos (not_le.mp h893).le h892 (not_le.mp h1012).le h1018
      · -- right
        exact CKLaneC2R.Cells.S00.B011.c220_pos (not_le.mp h893).le h892 (not_le.mp h1018).le h1017
    · -- right
      by_cases h1019 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B011.c223_pos (not_le.mp h893).le h892 (not_le.mp h1017).le h1019
      · -- right
        exact CKLaneC2R.Cells.S00.B011.c224_pos (not_le.mp h893).le h892 (not_le.mp h1019).le h989

end CKLaneC2R.CompactCover


