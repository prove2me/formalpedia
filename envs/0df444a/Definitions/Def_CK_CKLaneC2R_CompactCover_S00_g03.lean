-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g03
-- name    : CK_CKLaneC2R_CompactCover_S00_g03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T18:34:56.685423+00:00
-- url     : https://prove2.me/theorems/9784d0e5-219b-42ba-84b1-239e13cfbf23
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B033

namespace CKLaneC2R.CompactCover

theorem strip0_s004 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h6 : ¬ (a ≤ ((97/640 : ℚ) : ℝ))) (h32 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h33 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h44 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h45 : z ≤ ((10069/64000 : ℚ) : ℝ)
    · -- left
      by_cases h46 : z ≤ ((769/5120 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B055.c1110_pos (not_le.mp h6).le h3 (not_le.mp h33).le h46
      · -- right
        exact CKLaneC2R.Cells.S00.B055.c1111_pos (not_le.mp h6).le h3 (not_le.mp h46).le h45
    · -- right
      by_cases h47 : z ≤ ((21051/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B055.c1114_pos (not_le.mp h6).le h3 (not_le.mp h45).le h47
      · -- right
        exact CKLaneC2R.Cells.S00.B055.c1115_pos (not_le.mp h6).le h3 (not_le.mp h47).le h44
  · -- right
    by_cases h48 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      by_cases h49 : z ≤ ((22877/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B056.c1126_pos (not_le.mp h6).le h3 (not_le.mp h44).le h49
      · -- right
        exact CKLaneC2R.Cells.S00.B056.c1127_pos (not_le.mp h6).le h3 (not_le.mp h49).le h48
    · -- right
      exact CKLaneC2R.Cells.S00.B033.c673_pos (not_le.mp h6).le h3 (not_le.mp h48).le h32

end CKLaneC2R.CompactCover


