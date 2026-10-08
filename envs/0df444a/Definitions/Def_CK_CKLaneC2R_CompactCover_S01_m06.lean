-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m06
-- name    : CK_CKLaneC2R_CompactCover_S01_m06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T15:53:34.662276+00:00
-- url     : https://prove2.me/theorems/f82d3852-8771-4530-93de-c5cf09a1b4ef
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g46
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g47
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g48
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g49
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g50
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g51
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g52
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g53
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g54

namespace CKLaneC2R.CompactCover

theorem strip1_m06 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h598 : a ≤ ((39/160 : ℚ) : ℝ)
  · -- left
    by_cases h599 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h600 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h601 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h602 : a ≤ ((77/320 : ℚ) : ℝ)
          · -- left
            exact strip1_s060 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h599 h600 h601 h602
          · -- right
            exact strip1_s061 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h599 h600 h601 h602
        · -- right
          exact strip1_s062 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h599 h600 h601
      · -- right
        exact strip1_s063 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h599 h600
    · -- right
      by_cases h642 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip1_s064 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h599 h642
      · -- right
        by_cases h650 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s065 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h599 h642 h650
        · -- right
          by_cases h658 : z ≤ ((15071/16000 : ℚ) : ℝ)
          · -- left
            exact strip1_s066 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h599 h642 h650 h658
          · -- right
            exact strip1_s067 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h599 h642 h650 h658
  · -- right
    by_cases h675 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h676 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h677 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h678 : a ≤ ((79/320 : ℚ) : ℝ)
          · -- left
            exact strip1_s068 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h675 h676 h677 h678
          · -- right
            exact strip1_s069 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h675 h676 h677 h678
        · -- right
          exact strip1_s070 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h675 h676 h677
      · -- right
        exact strip1_s071 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h675 h676
    · -- right
      by_cases h715 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip1_s072 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h675 h715
      · -- right
        by_cases h723 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s073 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h675 h715 h723
        · -- right
          by_cases h730 : z ≤ ((15071/16000 : ℚ) : ℝ)
          · -- left
            exact strip1_s074 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h675 h715 h723 h730
          · -- right
            exact strip1_s075 ha1 ha2 hz1 hz2 h0 h1 h419 h598 h675 h715 h723 h730

end CKLaneC2R.CompactCover


