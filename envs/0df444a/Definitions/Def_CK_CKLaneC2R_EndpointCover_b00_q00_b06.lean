-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b06
-- name    : CK_CKLaneC2R_EndpointCover_b00_q00_b06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:05:25.343985+00:00
-- url     : https://prove2.me/theorems/cc767d1f-cb4f-4d67-8201-d6864a1ca499
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 7 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 7 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 7 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 7 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 1 of 5) (proof part 7 of 8).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B026
import Definitions.Def_CK_CKLaneC2R_EpCells_B027

namespace CKLaneC2R.EndpointCover

theorem cover_sub_000_sub_006 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : a ≤ ((39249/256000 : ℚ) : ℝ)) (h8 : a ≤ ((77649/512000 : ℚ) : ℝ)) (h9 : ¬ (a ≤ ((154449/1024000 : ℚ) : ℝ))) (h73 : ¬ (a ≤ ((309747/2048000 : ℚ) : ℝ))) (h105 : a ≤ ((620343/4096000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h106 : a ≤ ((1239837/8192000 : ℚ) : ℝ)
  · -- left
    by_cases h107 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h108 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h109 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1608_pos (not_le.mp h73).le h106 hz1 h109 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1610_pos (not_le.mp h73).le h106 (not_le.mp h109).le h108 hz
      · -- right
        by_cases h110 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1616_pos (not_le.mp h73).le h106 (not_le.mp h108).le h110 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1618_pos (not_le.mp h73).le h106 (not_le.mp h110).le h107 hz
    · -- right
      by_cases h111 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h112 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1640_pos (not_le.mp h73).le h106 (not_le.mp h107).le h112 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1642_pos (not_le.mp h73).le h106 (not_le.mp h112).le h111 hz
      · -- right
        by_cases h113 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1648_pos (not_le.mp h73).le h106 (not_le.mp h111).le h113 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1650_pos (not_le.mp h73).le h106 (not_le.mp h113).le hz2 hz
  · -- right
    by_cases h114 : z ≤ ((1999/2000 : ℚ) : ℝ)
    · -- left
      by_cases h115 : z ≤ ((3997/4000 : ℚ) : ℝ)
      · -- left
        by_cases h116 : z ≤ ((7993/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1609_pos (not_le.mp h106).le h105 hz1 h116 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1611_pos (not_le.mp h106).le h105 (not_le.mp h116).le h115 hz
      · -- right
        by_cases h117 : z ≤ ((1599/1600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B026.e1617_pos (not_le.mp h106).le h105 (not_le.mp h115).le h117 hz
        · -- right
          exact CKLaneC2R.EpCells.B026.e1619_pos (not_le.mp h106).le h105 (not_le.mp h117).le h114 hz
    · -- right
      by_cases h118 : z ≤ ((3999/4000 : ℚ) : ℝ)
      · -- left
        by_cases h119 : z ≤ ((7997/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1641_pos (not_le.mp h106).le h105 (not_le.mp h114).le h119 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1643_pos (not_le.mp h106).le h105 (not_le.mp h119).le h118 hz
      · -- right
        by_cases h120 : z ≤ ((7999/8000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.EpCells.B027.e1649_pos (not_le.mp h106).le h105 (not_le.mp h118).le h120 hz
        · -- right
          exact CKLaneC2R.EpCells.B027.e1651_pos (not_le.mp h106).le h105 (not_le.mp h120).le hz2 hz

end CKLaneC2R.EndpointCover


