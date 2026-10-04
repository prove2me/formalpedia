-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g00
-- name    : CK_CKLaneC2R_CompactCover_S00_g00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T09:58:55.693687+00:00
-- url     : https://prove2.me/theorems/741ed057-d07b-4903-8237-6f289f192fa4
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B068
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B069
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B053
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B054

namespace CKLaneC2R.CompactCover

theorem strip0_s000 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h6 : a ≤ ((97/640 : ℚ) : ℝ)) (h7 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h8 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h9 : z ≤ ((733/6400 : ℚ) : ℝ)
  · -- left
    by_cases h10 : z ≤ ((6417/64000 : ℚ) : ℝ)
    · -- left
      by_cases h11 : z ≤ ((11921/128000 : ℚ) : ℝ)
      · -- left
        by_cases h12 : z ≤ ((22929/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B068.c1370_pos ha1 h6 hz1 h12
        · -- right
          exact CKLaneC2R.Cells.S00.B068.c1371_pos ha1 h6 (not_le.mp h12).le h11
      · -- right
        by_cases h13 : z ≤ ((4951/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B068.c1374_pos ha1 h6 (not_le.mp h11).le h13
        · -- right
          exact CKLaneC2R.Cells.S00.B068.c1375_pos ha1 h6 (not_le.mp h13).le h10
    · -- right
      by_cases h14 : z ≤ ((13747/128000 : ℚ) : ℝ)
      · -- left
        by_cases h15 : z ≤ ((26581/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B069.c1386_pos ha1 h6 (not_le.mp h10).le h15
        · -- right
          exact CKLaneC2R.Cells.S00.B069.c1387_pos ha1 h6 (not_le.mp h15).le h14
      · -- right
        exact CKLaneC2R.Cells.S00.B053.c1060_pos ha1 h6 (not_le.mp h14).le h9
  · -- right
    by_cases h16 : z ≤ ((8243/64000 : ℚ) : ℝ)
    · -- left
      by_cases h17 : z ≤ ((15573/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B053.c1076_pos ha1 h6 (not_le.mp h9).le h17
      · -- right
        exact CKLaneC2R.Cells.S00.B053.c1078_pos ha1 h6 (not_le.mp h17).le h16
    · -- right
      by_cases h18 : z ≤ ((17399/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B054.c1084_pos ha1 h6 (not_le.mp h16).le h18
      · -- right
        exact CKLaneC2R.Cells.S00.B054.c1086_pos ha1 h6 (not_le.mp h18).le h8

end CKLaneC2R.CompactCover


