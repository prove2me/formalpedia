-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g63
-- name    : CK_CKLaneC2R_CompactCover_S00_g63
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T13:45:21.610591+00:00
-- url     : https://prove2.me/theorems/92b313a6-97dd-4738-9ef6-9e04ef1426f3
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B009

namespace CKLaneC2R.CompactCover

theorem strip0_s076 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : ¬ (a ≤ ((11/64 : ℚ) : ℝ))) (h794 : z ≤ ((217/400 : ℚ) : ℝ)) (h795 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h830 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h831 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h832 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h833 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B007.c145_pos (not_le.mp h693).le h0 (not_le.mp h795).le h833
        · -- right
          exact CKLaneC2R.Cells.S00.B007.c146_pos (not_le.mp h693).le h0 (not_le.mp h833).le h832
      · -- right
        by_cases h834 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B007.c149_pos (not_le.mp h693).le h0 (not_le.mp h832).le h834
        · -- right
          exact CKLaneC2R.Cells.S00.B007.c150_pos (not_le.mp h693).le h0 (not_le.mp h834).le h831
    · -- right
      by_cases h835 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h836 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B008.c161_pos (not_le.mp h693).le h0 (not_le.mp h831).le h836
        · -- right
          exact CKLaneC2R.Cells.S00.B008.c162_pos (not_le.mp h693).le h0 (not_le.mp h836).le h835
      · -- right
        by_cases h837 : z ≤ ((26503/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B008.c165_pos (not_le.mp h693).le h0 (not_le.mp h835).le h837
        · -- right
          exact CKLaneC2R.Cells.S00.B008.c166_pos (not_le.mp h693).le h0 (not_le.mp h837).le h830
  · -- right
    by_cases h838 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h839 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        by_cases h840 : z ≤ ((28329/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B008.c177_pos (not_le.mp h693).le h0 (not_le.mp h830).le h840
        · -- right
          exact CKLaneC2R.Cells.S00.B008.c178_pos (not_le.mp h693).le h0 (not_le.mp h840).le h839
      · -- right
        by_cases h841 : z ≤ ((6031/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B009.c181_pos (not_le.mp h693).le h0 (not_le.mp h839).le h841
        · -- right
          exact CKLaneC2R.Cells.S00.B009.c182_pos (not_le.mp h693).le h0 (not_le.mp h841).le h838
    · -- right
      by_cases h842 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        by_cases h843 : z ≤ ((31981/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B009.c193_pos (not_le.mp h693).le h0 (not_le.mp h838).le h843
        · -- right
          exact CKLaneC2R.Cells.S00.B009.c194_pos (not_le.mp h693).le h0 (not_le.mp h843).le h842
      · -- right
        by_cases h844 : z ≤ ((33807/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B009.c197_pos (not_le.mp h693).le h0 (not_le.mp h842).le h844
        · -- right
          exact CKLaneC2R.Cells.S00.B009.c198_pos (not_le.mp h693).le h0 (not_le.mp h844).le h794

end CKLaneC2R.CompactCover


