-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g70
-- name    : CK_CKLaneC2R_CompactCover_S00_g70
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T02:20:57.476006+00:00
-- url     : https://prove2.me/theorems/13f6380a-fbae-4fc3-8952-b4edebce4700
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B017

namespace CKLaneC2R.CompactCover

theorem strip0_s085 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : a ≤ ((57/320 : ℚ) : ℝ)) (h894 : z ≤ ((217/400 : ℚ) : ℝ)) (h895 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h928 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h929 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h930 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h931 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B013.c265_pos (not_le.mp h0).le h893 (not_le.mp h895).le h931
        · -- right
          exact CKLaneC2R.Cells.S00.B013.c266_pos (not_le.mp h0).le h893 (not_le.mp h931).le h930
      · -- right
        by_cases h932 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B013.c269_pos (not_le.mp h0).le h893 (not_le.mp h930).le h932
        · -- right
          exact CKLaneC2R.Cells.S00.B013.c270_pos (not_le.mp h0).le h893 (not_le.mp h932).le h929
    · -- right
      by_cases h933 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h934 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B014.c281_pos (not_le.mp h0).le h893 (not_le.mp h929).le h934
        · -- right
          exact CKLaneC2R.Cells.S00.B014.c282_pos (not_le.mp h0).le h893 (not_le.mp h934).le h933
      · -- right
        by_cases h935 : z ≤ ((26503/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B014.c285_pos (not_le.mp h0).le h893 (not_le.mp h933).le h935
        · -- right
          exact CKLaneC2R.Cells.S00.B014.c286_pos (not_le.mp h0).le h893 (not_le.mp h935).le h928
  · -- right
    by_cases h936 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h937 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        by_cases h938 : z ≤ ((28329/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B016.c321_pos (not_le.mp h0).le h893 (not_le.mp h928).le h938
        · -- right
          exact CKLaneC2R.Cells.S00.B016.c322_pos (not_le.mp h0).le h893 (not_le.mp h938).le h937
      · -- right
        by_cases h939 : z ≤ ((6031/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B016.c325_pos (not_le.mp h0).le h893 (not_le.mp h937).le h939
        · -- right
          exact CKLaneC2R.Cells.S00.B016.c326_pos (not_le.mp h0).le h893 (not_le.mp h939).le h936
    · -- right
      by_cases h940 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        by_cases h941 : z ≤ ((31981/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B016.c335_pos (not_le.mp h0).le h893 (not_le.mp h936).le h941
        · -- right
          exact CKLaneC2R.Cells.S00.B016.c336_pos (not_le.mp h0).le h893 (not_le.mp h941).le h940
      · -- right
        by_cases h942 : z ≤ ((33807/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B016.c339_pos (not_le.mp h0).le h893 (not_le.mp h940).le h942
        · -- right
          exact CKLaneC2R.Cells.S00.B017.c340_pos (not_le.mp h0).le h893 (not_le.mp h942).le h894

end CKLaneC2R.CompactCover


