-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b01
-- name    : CK_CKLaneC2R_EndpointCover_b00_q00_b01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:07:24.221784+00:00
-- url     : https://prove2.me/theorems/1dd59883-b823-44f4-8593-d2fc22c5b735
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 2 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 2 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 2 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 2 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 2 of 8).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B025
import Definitions.Def_CK_CKLaneC2R_EpCells_B026

namespace CKLaneC2R.EndpointCover

theorem cover_sub_000_sub_001 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : a ≤ ((39249/256000 : ℚ) : ℝ)) (h8 : a ≤ ((77649/512000 : ℚ) : ℝ)) (h9 : a ≤ ((154449/1024000 : ℚ) : ℝ)) (h10 : a ≤ ((308049/2048000 : ℚ) : ℝ)) (h11 : ¬ (a ≤ ((615249/4096000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h27 : a ≤ ((1231347/8192000 : ℚ) : ℝ)
  · -- left
    by_cases h28 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h29 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h30 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1532_pos (not_le.mp h11).le h27 hz1 h30 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1534_pos (not_le.mp h11).le h27 (not_le.mp h30).le h29 hz
      · -- right
        by_cases h31 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1540_pos (not_le.mp h11).le h27 (not_le.mp h29).le h31 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1542_pos (not_le.mp h11).le h27 (not_le.mp h31).le h28 hz
    · -- right
      by_cases h32 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h33 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1564_pos (not_le.mp h11).le h27 (not_le.mp h28).le h33 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1566_pos (not_le.mp h11).le h27 (not_le.mp h33).le h32 hz
      · -- right
        by_cases h34 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1572_pos (not_le.mp h11).le h27 (not_le.mp h32).le h34 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1574_pos (not_le.mp h11).le h27 (not_le.mp h34).le hz2 hz
  · -- right
    by_cases h35 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h36 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h37 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1533_pos (not_le.mp h27).le h10 hz1 h37 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1535_pos (not_le.mp h27).le h10 (not_le.mp h37).le h36 hz
      · -- right
        by_cases h38 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1541_pos (not_le.mp h27).le h10 (not_le.mp h36).le h38 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1543_pos (not_le.mp h27).le h10 (not_le.mp h38).le h35 hz
    · -- right
      by_cases h39 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h40 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1565_pos (not_le.mp h27).le h10 (not_le.mp h35).le h40 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1567_pos (not_le.mp h27).le h10 (not_le.mp h40).le h39 hz
      · -- right
        by_cases h41 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1573_pos (not_le.mp h27).le h10 (not_le.mp h39).le h41 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1575_pos (not_le.mp h27).le h10 (not_le.mp h41).le hz2 hz

end CKLaneC2R.EndpointCover


