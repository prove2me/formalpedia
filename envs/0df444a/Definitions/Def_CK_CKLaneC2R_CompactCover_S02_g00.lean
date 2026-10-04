-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g00
-- name    : CK_CKLaneC2R_CompactCover_S02_g00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T18:23:17.261987+00:00
-- url     : https://prove2.me/theorems/52cb9f8e-1bbc-4365-814c-4f7bf7afb1a4
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B037
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B038
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B014

namespace CKLaneC2R.CompactCover

theorem strip2_s000 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : a ≤ ((5/16 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : a ≤ ((49/160 : ℚ) : ℝ)) (h6 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h7 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h8 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h9 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h10 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h11 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B037.c755_pos ha1 h5 hz1 h11
          · -- right
            exact CKLaneC2R.Cells.S02.B037.c756_pos ha1 h5 (not_le.mp h11).le h10
        · -- right
          by_cases h12 : z ≤ ((13747/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B037.c759_pos ha1 h5 (not_le.mp h10).le h12
          · -- right
            exact CKLaneC2R.Cells.S02.B038.c760_pos ha1 h5 (not_le.mp h12).le h9
      · -- right
        by_cases h13 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B028.c579_pos ha1 h5 (not_le.mp h9).le h13
        · -- right
          exact CKLaneC2R.Cells.S02.B029.c581_pos ha1 h5 (not_le.mp h13).le h8
    · -- right
      by_cases h14 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h15 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B029.c587_pos ha1 h5 (not_le.mp h8).le h15
        · -- right
          exact CKLaneC2R.Cells.S02.B029.c588_pos ha1 h5 (not_le.mp h15).le h14
      · -- right
        by_cases h16 : z ≤ ((2379/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B029.c591_pos ha1 h5 (not_le.mp h14).le h16
        · -- right
          exact CKLaneC2R.Cells.S02.B029.c592_pos ha1 h5 (not_le.mp h16).le h7
  · -- right
    by_cases h17 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h18 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h19 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B031.c629_pos ha1 h5 (not_le.mp h7).le h19
        · -- right
          exact CKLaneC2R.Cells.S02.B031.c630_pos ha1 h5 (not_le.mp h19).le h18
      · -- right
        exact CKLaneC2R.Cells.S02.B014.c291_pos ha1 h5 (not_le.mp h18).le h17
    · -- right
      by_cases h20 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B014.c296_pos ha1 h5 (not_le.mp h17).le h20
      · -- right
        exact CKLaneC2R.Cells.S02.B014.c298_pos ha1 h5 (not_le.mp h20).le h6

end CKLaneC2R.CompactCover


