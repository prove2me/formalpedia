-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m10
-- name    : CK_CKLaneC2R_CompactCover_S00_m10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T19:02:32.230494+00:00
-- url     : https://prove2.me/theorems/a7652836-4e56-438e-acb7-bc24c9264d59
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g81
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g82
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g83
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g84
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g85
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g86
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g87
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g88
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g89
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g90

namespace CKLaneC2R.CompactCover

theorem strip0_m10 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1078 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h1079 : a ≤ ((59/320 : ℚ) : ℝ)
    · -- left
      by_cases h1080 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h1081 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h1082 : z ≤ ((2289/16000 : ℚ) : ℝ)
          · -- left
            exact strip0_s099 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1079 h1080 h1081 h1082
          · -- right
            exact strip0_s100 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1079 h1080 h1081 h1082
        · -- right
          exact strip0_s101 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1079 h1080 h1081
      · -- right
        exact strip0_s102 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1079 h1080
    · -- right
      by_cases h1124 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h1125 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h1126 : z ≤ ((2289/16000 : ℚ) : ℝ)
          · -- left
            exact strip0_s103 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1079 h1124 h1125 h1126
          · -- right
            exact strip0_s104 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1079 h1124 h1125 h1126
        · -- right
          exact strip0_s105 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1079 h1124 h1125
      · -- right
        exact strip0_s106 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1079 h1124
  · -- right
    by_cases h1164 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      by_cases h1165 : a ≤ ((59/320 : ℚ) : ℝ)
      · -- left
        exact strip0_s107 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1164 h1165
      · -- right
        exact strip0_s108 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1164 h1165
    · -- right
      by_cases h1185 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s109 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1164 h1185
      · -- right
        by_cases h1201 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s110 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1164 h1185 h1201
        · -- right
          by_cases h1211 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip0_s111 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1164 h1185 h1201 h1211
          · -- right
            by_cases h1219 : z ≤ ((63023/64000 : ℚ) : ℝ)
            · -- left
              exact strip0_s112 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1164 h1185 h1201 h1211 h1219
            · -- right
              exact strip0_s113 ha1 ha2 hz1 hz2 h0 h891 h892 h1078 h1164 h1185 h1201 h1211 h1219

end CKLaneC2R.CompactCover


