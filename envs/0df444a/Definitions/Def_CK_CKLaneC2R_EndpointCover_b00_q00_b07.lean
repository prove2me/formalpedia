-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b07
-- name    : CK_CKLaneC2R_EndpointCover_b00_q00_b07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:03:25.21021+00:00
-- url     : https://prove2.me/theorems/80fe11c2-c3af-4fe2-b431-802de6bc5708
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 8 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 8 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 8 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 8 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 8 of 8).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B026
import Definitions.Def_CK_CKLaneC2R_EpCells_B027

namespace CKLaneC2R.EndpointCover

theorem cover_sub_000_sub_007 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : a ≤ ((39249/256000 : ℚ) : ℝ)) (h8 : a ≤ ((77649/512000 : ℚ) : ℝ)) (h9 : ¬ (a ≤ ((154449/1024000 : ℚ) : ℝ))) (h73 : ¬ (a ≤ ((309747/2048000 : ℚ) : ℝ))) (h105 : ¬ (a ≤ ((620343/4096000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h121 : a ≤ ((248307/1638400 : ℚ) : ℝ)
  · -- left
    by_cases h122 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h123 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h124 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1612_pos (not_le.mp h105).le h121 hz1 h124 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1614_pos (not_le.mp h105).le h121 (not_le.mp h124).le h123 hz
      · -- right
        by_cases h125 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1620_pos (not_le.mp h105).le h121 (not_le.mp h123).le h125 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1622_pos (not_le.mp h105).le h121 (not_le.mp h125).le h122 hz
    · -- right
      by_cases h126 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h127 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1644_pos (not_le.mp h105).le h121 (not_le.mp h122).le h127 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1646_pos (not_le.mp h105).le h121 (not_le.mp h127).le h126 hz
      · -- right
        by_cases h128 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1652_pos (not_le.mp h105).le h121 (not_le.mp h126).le h128 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1654_pos (not_le.mp h105).le h121 (not_le.mp h128).le hz2 hz
  · -- right
    by_cases h129 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h130 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h131 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1613_pos (not_le.mp h121).le h8 hz1 h131 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1615_pos (not_le.mp h121).le h8 (not_le.mp h131).le h130 hz
      · -- right
        by_cases h132 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1621_pos (not_le.mp h121).le h8 (not_le.mp h130).le h132 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1623_pos (not_le.mp h121).le h8 (not_le.mp h132).le h129 hz
    · -- right
      by_cases h133 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h134 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1645_pos (not_le.mp h121).le h8 (not_le.mp h129).le h134 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1647_pos (not_le.mp h121).le h8 (not_le.mp h134).le h133 hz
      · -- right
        by_cases h135 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1653_pos (not_le.mp h121).le h8 (not_le.mp h133).le h135 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1655_pos (not_le.mp h121).le h8 (not_le.mp h135).le hz2 hz

end CKLaneC2R.EndpointCover


