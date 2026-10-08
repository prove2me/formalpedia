-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m00
-- name    : CK_CKLaneC2R_CompactCover_S05_m00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T16:59:37.878616+00:00
-- url     : https://prove2.me/theorems/2dab1c54-5643-403d-b04f-5b0eb4208f09
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g00
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g01
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g02
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g03
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g04
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g05
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g06
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g07
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g08
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g09
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g10
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g11

namespace CKLaneC2R.CompactCover

theorem strip5_m00 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1 : a ≤ ((3699/4000 : ℚ) : ℝ)
  · -- left
    by_cases h2 : a ≤ ((7299/8000 : ℚ) : ℝ)
    · -- left
      by_cases h3 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s000 ha1 ha2 hz1 hz2 h0 h1 h2 h3
      · -- right
        by_cases h12 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s001 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h12
        · -- right
          exact strip5_s002 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h12
    · -- right
      by_cases h34 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s003 ha1 ha2 hz1 hz2 h0 h1 h2 h34
      · -- right
        by_cases h43 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s004 ha1 ha2 hz1 hz2 h0 h1 h2 h34 h43
        · -- right
          by_cases h48 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s005 ha1 ha2 hz1 hz2 h0 h1 h2 h34 h43 h48
          · -- right
            by_cases h52 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s006 ha1 ha2 hz1 hz2 h0 h1 h2 h34 h43 h48 h52
            · -- right
              exact strip5_s007 ha1 ha2 hz1 hz2 h0 h1 h2 h34 h43 h48 h52
  · -- right
    by_cases h69 : a ≤ ((7497/8000 : ℚ) : ℝ)
    · -- left
      by_cases h70 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s008 ha1 ha2 hz1 hz2 h0 h1 h69 h70
      · -- right
        by_cases h79 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s009 ha1 ha2 hz1 hz2 h0 h1 h69 h70 h79
        · -- right
          by_cases h84 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s010 ha1 ha2 hz1 hz2 h0 h1 h69 h70 h79 h84
          · -- right
            by_cases h89 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s011 ha1 ha2 hz1 hz2 h0 h1 h69 h70 h79 h84 h89
            · -- right
              exact strip5_s012 ha1 ha2 hz1 hz2 h0 h1 h69 h70 h79 h84 h89
    · -- right
      by_cases h107 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s013 ha1 ha2 hz1 hz2 h0 h1 h69 h107
      · -- right
        by_cases h116 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s014 ha1 ha2 hz1 hz2 h0 h1 h69 h107 h116
        · -- right
          by_cases h121 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s015 ha1 ha2 hz1 hz2 h0 h1 h69 h107 h116 h121
          · -- right
            by_cases h126 : a ≤ ((15093/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s016 ha1 ha2 hz1 hz2 h0 h1 h69 h107 h116 h121 h126
            · -- right
              exact strip5_s017 ha1 ha2 hz1 hz2 h0 h1 h69 h107 h116 h121 h126

end CKLaneC2R.CompactCover


