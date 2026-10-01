-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b02
-- name    : CK_CKLaneC2R_EndpointCover_b00_q00_b02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:07:04.770974+00:00
-- url     : https://prove2.me/theorems/3b225f8d-5ad3-4676-8e22-f14645a3476a
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 3 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 3 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 3 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 3 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 3 of 8).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B025
import Definitions.Def_CK_CKLaneC2R_EpCells_B026

namespace CKLaneC2R.EndpointCover

theorem cover_sub_000_sub_002 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : a ≤ ((39249/256000 : ℚ) : ℝ)) (h8 : a ≤ ((77649/512000 : ℚ) : ℝ)) (h9 : a ≤ ((154449/1024000 : ℚ) : ℝ)) (h10 : ¬ (a ≤ ((308049/2048000 : ℚ) : ℝ))) (h42 : a ≤ ((616947/4096000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h43 : a ≤ ((246609/1638400 : ℚ) : ℝ)
  · -- left
    by_cases h44 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h45 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h46 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1544_pos (not_le.mp h10).le h43 hz1 h46 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1546_pos (not_le.mp h10).le h43 (not_le.mp h46).le h45 hz
      · -- right
        by_cases h47 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1552_pos (not_le.mp h10).le h43 (not_le.mp h45).le h47 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1554_pos (not_le.mp h10).le h43 (not_le.mp h47).le h44 hz
    · -- right
      by_cases h48 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h49 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1576_pos (not_le.mp h10).le h43 (not_le.mp h44).le h49 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1578_pos (not_le.mp h10).le h43 (not_le.mp h49).le h48 hz
      · -- right
        by_cases h50 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1584_pos (not_le.mp h10).le h43 (not_le.mp h48).le h50 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1586_pos (not_le.mp h10).le h43 (not_le.mp h50).le hz2 hz
  · -- right
    by_cases h51 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h52 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h53 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1545_pos (not_le.mp h43).le h42 hz1 h53 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1547_pos (not_le.mp h43).le h42 (not_le.mp h53).le h52 hz
      · -- right
        by_cases h54 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B025.e1553_pos (not_le.mp h43).le h42 (not_le.mp h52).le h54 hz
        · -- right
          exact CKLaneC2R.EpCells.B025.e1555_pos (not_le.mp h43).le h42 (not_le.mp h54).le h51 hz
    · -- right
      by_cases h55 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h56 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1577_pos (not_le.mp h43).le h42 (not_le.mp h51).le h56 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1579_pos (not_le.mp h43).le h42 (not_le.mp h56).le h55 hz
      · -- right
        by_cases h57 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1585_pos (not_le.mp h43).le h42 (not_le.mp h55).le h57 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1587_pos (not_le.mp h43).le h42 (not_le.mp h57).le hz2 hz

end CKLaneC2R.EndpointCover


