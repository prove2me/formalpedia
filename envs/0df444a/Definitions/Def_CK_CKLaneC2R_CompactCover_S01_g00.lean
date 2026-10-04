-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g00
-- name    : CK_CKLaneC2R_CompactCover_S01_g00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T04:48:38.523281+00:00
-- url     : https://prove2.me/theorems/878f1c3c-230e-421f-800f-514ddf8e35f3
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B047
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B048
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B050
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B032

namespace CKLaneC2R.CompactCover

theorem strip1_s000 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : a ≤ ((33/160 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : a ≤ ((13/64 : ℚ) : ℝ)) (h6 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h7 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h8 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h9 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h10 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h11 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          by_cases h12 : a ≤ ((129/640 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B056.c1129_pos ha1 h12 hz1 h11
          · -- right
            exact CKLaneC2R.Cells.S01.B056.c1130_pos (not_le.mp h12).le h5 hz1 h11
        · -- right
          exact CKLaneC2R.Cells.S01.B047.c950_pos ha1 h5 (not_le.mp h11).le h10
      · -- right
        by_cases h13 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B047.c952_pos ha1 h5 (not_le.mp h10).le h13
        · -- right
          exact CKLaneC2R.Cells.S01.B047.c953_pos ha1 h5 (not_le.mp h13).le h9
    · -- right
      by_cases h14 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h15 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B048.c964_pos ha1 h5 (not_le.mp h9).le h15
        · -- right
          exact CKLaneC2R.Cells.S01.B048.c965_pos ha1 h5 (not_le.mp h15).le h14
      · -- right
        by_cases h16 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B048.c968_pos ha1 h5 (not_le.mp h14).le h16
        · -- right
          exact CKLaneC2R.Cells.S01.B048.c969_pos ha1 h5 (not_le.mp h16).le h8
  · -- right
    by_cases h17 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h18 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h19 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B050.c1008_pos ha1 h5 (not_le.mp h8).le h19
        · -- right
          exact CKLaneC2R.Cells.S01.B050.c1009_pos ha1 h5 (not_le.mp h19).le h18
      · -- right
        exact CKLaneC2R.Cells.S01.B031.c634_pos ha1 h5 (not_le.mp h18).le h17
    · -- right
      by_cases h20 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B031.c639_pos ha1 h5 (not_le.mp h17).le h20
      · -- right
        exact CKLaneC2R.Cells.S01.B032.c641_pos ha1 h5 (not_le.mp h20).le h7

end CKLaneC2R.CompactCover


