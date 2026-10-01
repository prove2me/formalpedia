-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b04
-- name    : CK_CKLaneC2R_EndpointCover_b00_q00_b04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:08:56.303983+00:00
-- url     : https://prove2.me/theorems/ce6e24f0-78f1-4647-9a14-a9c46c14667f
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 5 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 5 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 5 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 5 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 5 of 8).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B026
import Definitions.Def_CK_CKLaneC2R_EpCells_B027

namespace CKLaneC2R.EndpointCover

theorem cover_sub_000_sub_004 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : a ≤ ((39249/256000 : ℚ) : ℝ)) (h8 : a ≤ ((77649/512000 : ℚ) : ℝ)) (h9 : ¬ (a ≤ ((154449/1024000 : ℚ) : ℝ))) (h73 : a ≤ ((309747/2048000 : ℚ) : ℝ)) (h74 : a ≤ ((123729/819200 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h75 : a ≤ ((1236441/8192000 : ℚ) : ℝ)
  · -- left
    by_cases h76 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h77 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h78 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1592_pos (not_le.mp h9).le h75 hz1 h78 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1594_pos (not_le.mp h9).le h75 (not_le.mp h78).le h77 hz
      · -- right
        by_cases h79 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1600_pos (not_le.mp h9).le h75 (not_le.mp h77).le h79 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1602_pos (not_le.mp h9).le h75 (not_le.mp h79).le h76 hz
    · -- right
      by_cases h80 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h81 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1624_pos (not_le.mp h9).le h75 (not_le.mp h76).le h81 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1626_pos (not_le.mp h9).le h75 (not_le.mp h81).le h80 hz
      · -- right
        by_cases h82 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1632_pos (not_le.mp h9).le h75 (not_le.mp h80).le h82 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1634_pos (not_le.mp h9).le h75 (not_le.mp h82).le hz2 hz
  · -- right
    by_cases h83 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h84 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h85 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1593_pos (not_le.mp h75).le h74 hz1 h85 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1595_pos (not_le.mp h75).le h74 (not_le.mp h85).le h84 hz
      · -- right
        by_cases h86 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1601_pos (not_le.mp h75).le h74 (not_le.mp h84).le h86 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1603_pos (not_le.mp h75).le h74 (not_le.mp h86).le h83 hz
    · -- right
      by_cases h87 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h88 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1625_pos (not_le.mp h75).le h74 (not_le.mp h83).le h88 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1627_pos (not_le.mp h75).le h74 (not_le.mp h88).le h87 hz
      · -- right
        by_cases h89 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1633_pos (not_le.mp h75).le h74 (not_le.mp h87).le h89 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1635_pos (not_le.mp h75).le h74 (not_le.mp h89).le hz2 hz

end CKLaneC2R.EndpointCover


