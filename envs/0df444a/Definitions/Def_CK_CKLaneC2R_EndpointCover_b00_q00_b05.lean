-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b05
-- name    : CK_CKLaneC2R_EndpointCover_b00_q00_b05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:03:34.662977+00:00
-- url     : https://prove2.me/theorems/186b266d-c16c-4c1d-838f-665289aa5283
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 6 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 6 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 6 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 6 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 6 of 8).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B026
import Definitions.Def_CK_CKLaneC2R_EpCells_B027

namespace CKLaneC2R.EndpointCover

theorem cover_sub_000_sub_005 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : a ≤ ((39249/256000 : ℚ) : ℝ)) (h8 : a ≤ ((77649/512000 : ℚ) : ℝ)) (h9 : ¬ (a ≤ ((154449/1024000 : ℚ) : ℝ))) (h73 : a ≤ ((309747/2048000 : ℚ) : ℝ)) (h74 : ¬ (a ≤ ((123729/819200 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h90 : a ≤ ((1238139/8192000 : ℚ) : ℝ)
  · -- left
    by_cases h91 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h92 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h93 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1596_pos (not_le.mp h74).le h90 hz1 h93 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1598_pos (not_le.mp h74).le h90 (not_le.mp h93).le h92 hz
      · -- right
        by_cases h94 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1604_pos (not_le.mp h74).le h90 (not_le.mp h92).le h94 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1606_pos (not_le.mp h74).le h90 (not_le.mp h94).le h91 hz
    · -- right
      by_cases h95 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h96 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1628_pos (not_le.mp h74).le h90 (not_le.mp h91).le h96 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1630_pos (not_le.mp h74).le h90 (not_le.mp h96).le h95 hz
      · -- right
        by_cases h97 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1636_pos (not_le.mp h74).le h90 (not_le.mp h95).le h97 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1638_pos (not_le.mp h74).le h90 (not_le.mp h97).le hz2 hz
  · -- right
    by_cases h98 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h99 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h100 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1597_pos (not_le.mp h90).le h73 hz1 h100 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1599_pos (not_le.mp h90).le h73 (not_le.mp h100).le h99 hz
      · -- right
        by_cases h101 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1605_pos (not_le.mp h90).le h73 (not_le.mp h99).le h101 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1607_pos (not_le.mp h90).le h73 (not_le.mp h101).le h98 hz
    · -- right
      by_cases h102 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h103 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1629_pos (not_le.mp h90).le h73 (not_le.mp h98).le h103 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1631_pos (not_le.mp h90).le h73 (not_le.mp h103).le h102 hz
      · -- right
        by_cases h104 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1637_pos (not_le.mp h90).le h73 (not_le.mp h102).le h104 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1639_pos (not_le.mp h90).le h73 (not_le.mp h104).le hz2 hz

end CKLaneC2R.EndpointCover


