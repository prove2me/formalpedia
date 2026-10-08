-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m05
-- name    : CK_CKLaneC2R_CompactCover_S05_m05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T21:23:56.600994+00:00
-- url     : https://prove2.me/theorems/958e7c9a-9191-4901-8f93-8292fb3cf3f7
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g47
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g48
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g49
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g50
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g51
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g52
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g53
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g54

namespace CKLaneC2R.CompactCover

theorem strip5_m05 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : a ≤ ((63837/64000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h551 : a ≤ ((5103/5120 : ℚ) : ℝ)
  · -- left
    by_cases h552 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      exact strip5_s085 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h552
    · -- right
      by_cases h557 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip5_s086 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h552 h557
      · -- right
        by_cases h560 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip5_s087 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h552 h557 h560
        · -- right
          by_cases h563 : z ≤ ((15071/16000 : ℚ) : ℝ)
          · -- left
            exact strip5_s088 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h552 h557 h560 h563
          · -- right
            by_cases h566 : z ≤ ((6211/6400 : ℚ) : ℝ)
            · -- left
              exact strip5_s089 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h552 h557 h560 h563 h566
            · -- right
              exact strip5_s090 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h552 h557 h560 h563 h566
  · -- right
    by_cases h582 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      exact strip5_s091 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h582
    · -- right
      by_cases h588 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip5_s092 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h582 h588
      · -- right
        by_cases h591 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip5_s093 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h582 h588 h591
        · -- right
          by_cases h594 : z ≤ ((15071/16000 : ℚ) : ℝ)
          · -- left
            exact strip5_s094 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h582 h588 h591 h594
          · -- right
            by_cases h597 : z ≤ ((6211/6400 : ℚ) : ℝ)
            · -- left
              exact strip5_s095 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h582 h588 h591 h594 h597
            · -- right
              by_cases h600 : z ≤ ((63023/64000 : ℚ) : ℝ)
              · -- left
                exact strip5_s096 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h582 h588 h591 h594 h597 h600
              · -- right
                by_cases h603 : z ≤ ((126959/128000 : ℚ) : ℝ)
                · -- left
                  exact strip5_s097 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h582 h588 h591 h594 h597 h600 h603
                · -- right
                  exact strip5_s098 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h551 h582 h588 h591 h594 h597 h600 h603

end CKLaneC2R.CompactCover


