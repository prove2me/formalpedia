-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b03
-- name    : CK_CKLaneC2R_EndpointCover_b00_q00_b03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:07:20.262661+00:00
-- url     : https://prove2.me/theorems/9343c7b7-978c-4b59-91e4-7433b80d7c61
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 4 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 4 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 4 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 4 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 4 of 8).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B025
import Definitions.Def_CK_CKLaneC2R_EpCells_B026

namespace CKLaneC2R.EndpointCover

theorem cover_sub_000_sub_003 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : a ≤ ((39249/256000 : ℚ) : ℝ)) (h8 : a ≤ ((77649/512000 : ℚ) : ℝ)) (h9 : a ≤ ((154449/1024000 : ℚ) : ℝ)) (h10 : ¬ (a ≤ ((308049/2048000 : ℚ) : ℝ))) (h42 : ¬ (a ≤ ((616947/4096000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h58 : a ≤ ((1234743/8192000 : ℚ) : ℝ)
  · -- left
    by_cases h59 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h60 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h61 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1548_pos (not_le.mp h42).le h58 hz1 h61 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1550_pos (not_le.mp h42).le h58 (not_le.mp h61).le h60 hz
      · -- right
        by_cases h62 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1556_pos (not_le.mp h42).le h58 (not_le.mp h60).le h62 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1558_pos (not_le.mp h42).le h58 (not_le.mp h62).le h59 hz
    · -- right
      by_cases h63 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h64 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1580_pos (not_le.mp h42).le h58 (not_le.mp h59).le h64 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1582_pos (not_le.mp h42).le h58 (not_le.mp h64).le h63 hz
      · -- right
        by_cases h65 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1588_pos (not_le.mp h42).le h58 (not_le.mp h63).le h65 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1590_pos (not_le.mp h42).le h58 (not_le.mp h65).le hz2 hz
  · -- right
    by_cases h66 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h67 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h68 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1549_pos (not_le.mp h58).le h9 hz1 h68 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1551_pos (not_le.mp h58).le h9 (not_le.mp h68).le h67 hz
      · -- right
        by_cases h69 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1557_pos (not_le.mp h58).le h9 (not_le.mp h67).le h69 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1559_pos (not_le.mp h58).le h9 (not_le.mp h69).le h66 hz
    · -- right
      by_cases h70 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h71 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1581_pos (not_le.mp h58).le h9 (not_le.mp h66).le h71 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1583_pos (not_le.mp h58).le h9 (not_le.mp h71).le h70 hz
      · -- right
        by_cases h72 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1589_pos (not_le.mp h58).le h9 (not_le.mp h70).le h72 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1591_pos (not_le.mp h58).le h9 (not_le.mp h72).le hz2 hz

end CKLaneC2R.EndpointCover


