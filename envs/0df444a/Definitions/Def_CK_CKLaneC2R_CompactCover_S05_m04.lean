-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m04
-- name    : CK_CKLaneC2R_CompactCover_S05_m04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T20:55:28.495375+00:00
-- url     : https://prove2.me/theorems/f38a50bc-ccf8-4e7a-8fee-12efaa4b4546
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g39
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g40
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g41
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g42
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g43
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g44
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g45
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g46

namespace CKLaneC2R.CompactCover

theorem strip5_m04 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : a ≤ ((31869/32000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h474 : a ≤ ((63639/64000 : ℚ) : ℝ)
  · -- left
    by_cases h475 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      exact strip5_s070 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h475
    · -- right
      by_cases h480 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip5_s071 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h475 h480
      · -- right
        by_cases h483 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip5_s072 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h475 h480 h483
        · -- right
          by_cases h486 : z ≤ ((15071/16000 : ℚ) : ℝ)
          · -- left
            exact strip5_s073 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h475 h480 h483 h486
          · -- right
            by_cases h489 : z ≤ ((6211/6400 : ℚ) : ℝ)
            · -- left
              exact strip5_s074 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h475 h480 h483 h486 h489
            · -- right
              by_cases h492 : z ≤ ((63023/64000 : ℚ) : ℝ)
              · -- left
                exact strip5_s075 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h475 h480 h483 h486 h489 h492
              · -- right
                exact strip5_s076 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h475 h480 h483 h486 h489 h492
  · -- right
    by_cases h507 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      exact strip5_s077 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h507
    · -- right
      by_cases h516 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip5_s078 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h507 h516
      · -- right
        by_cases h520 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip5_s079 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h507 h516 h520
        · -- right
          by_cases h523 : z ≤ ((15071/16000 : ℚ) : ℝ)
          · -- left
            exact strip5_s080 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h507 h516 h520 h523
          · -- right
            by_cases h526 : z ≤ ((6211/6400 : ℚ) : ℝ)
            · -- left
              exact strip5_s081 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h507 h516 h520 h523 h526
            · -- right
              by_cases h530 : z ≤ ((63023/64000 : ℚ) : ℝ)
              · -- left
                exact strip5_s082 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h507 h516 h520 h523 h526 h530
              · -- right
                by_cases h535 : a ≤ ((127377/128000 : ℚ) : ℝ)
                · -- left
                  exact strip5_s083 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h507 h516 h520 h523 h526 h530 h535
                · -- right
                  exact strip5_s084 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h474 h507 h516 h520 h523 h526 h530 h535

end CKLaneC2R.CompactCover


