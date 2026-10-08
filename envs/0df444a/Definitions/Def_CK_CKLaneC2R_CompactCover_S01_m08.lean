-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m08
-- name    : CK_CKLaneC2R_CompactCover_S01_m08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T20:23:35.131979+00:00
-- url     : https://prove2.me/theorems/be22f356-2934-4278-a5a0-90146e733250
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g64
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g65
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g66
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g67
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g68
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g69
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g70
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g71

namespace CKLaneC2R.CompactCover

theorem strip1_m08 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h880 : a ≤ ((43/160 : ℚ) : ℝ)
  · -- left
    by_cases h881 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h882 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h883 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s091 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h881 h882 h883
        · -- right
          exact strip1_s092 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h881 h882 h883
      · -- right
        exact strip1_s093 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h881 h882
    · -- right
      by_cases h914 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip1_s094 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h881 h914
      · -- right
        by_cases h922 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s095 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h881 h914 h922
        · -- right
          exact strip1_s096 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h881 h914 h922
  · -- right
    by_cases h941 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h942 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h943 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s097 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h941 h942 h943
        · -- right
          exact strip1_s098 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h941 h942 h943
      · -- right
        exact strip1_s099 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h941 h942
    · -- right
      by_cases h971 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip1_s100 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h941 h971
      · -- right
        by_cases h979 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s101 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h941 h971 h979
        · -- right
          exact strip1_s102 ha1 ha2 hz1 hz2 h0 h746 h747 h880 h941 h971 h979

end CKLaneC2R.CompactCover


