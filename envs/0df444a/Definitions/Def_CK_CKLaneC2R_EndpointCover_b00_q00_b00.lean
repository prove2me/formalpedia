-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b00
-- name    : CK_CKLaneC2R_EndpointCover_b00_q00_b00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:05:22.109979+00:00
-- url     : https://prove2.me/theorems/fd260fd5-ca60-42c2-a7e8-a72c363a4e5f
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 1 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 1 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 1 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 1 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 1 of 8).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B025
import Definitions.Def_CK_CKLaneC2R_EpCells_B026

namespace CKLaneC2R.EndpointCover

theorem cover_sub_000_sub_000 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : a ≤ ((39249/256000 : ℚ) : ℝ)) (h8 : a ≤ ((77649/512000 : ℚ) : ℝ)) (h9 : a ≤ ((154449/1024000 : ℚ) : ℝ)) (h10 : a ≤ ((308049/2048000 : ℚ) : ℝ)) (h11 : a ≤ ((615249/4096000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h12 : a ≤ ((1229649/8192000 : ℚ) : ℝ)
  · -- left
    by_cases h13 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h14 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h15 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1528_pos ha1 h12 hz1 h15 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1530_pos ha1 h12 (not_le.mp h15).le h14 hz
      · -- right
        by_cases h16 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1536_pos ha1 h12 (not_le.mp h14).le h16 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1538_pos ha1 h12 (not_le.mp h16).le h13 hz
    · -- right
      by_cases h17 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h18 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1560_pos ha1 h12 (not_le.mp h13).le h18 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1562_pos ha1 h12 (not_le.mp h18).le h17 hz
      · -- right
        by_cases h19 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1568_pos ha1 h12 (not_le.mp h17).le h19 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1570_pos ha1 h12 (not_le.mp h19).le hz2 hz
  · -- right
    by_cases h20 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h21 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h22 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1529_pos (not_le.mp h12).le h11 hz1 h22 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1531_pos (not_le.mp h12).le h11 (not_le.mp h22).le h21 hz
      · -- right
        by_cases h23 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1537_pos (not_le.mp h12).le h11 (not_le.mp h21).le h23 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1539_pos (not_le.mp h12).le h11 (not_le.mp h23).le h20 hz
    · -- right
      by_cases h24 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h25 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1561_pos (not_le.mp h12).le h11 (not_le.mp h20).le h25 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1563_pos (not_le.mp h12).le h11 (not_le.mp h25).le h24 hz
      · -- right
        by_cases h26 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1569_pos (not_le.mp h12).le h11 (not_le.mp h24).le h26 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1571_pos (not_le.mp h12).le h11 (not_le.mp h26).le hz2 hz

end CKLaneC2R.EndpointCover


