-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m06
-- name    : CK_CKLaneC2R_CompactCover_S05_m06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T19:36:05.443161+00:00
-- url     : https://prove2.me/theorems/8fab6001-6963-4843-a00c-b497f9421da6
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g55
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g56
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g57
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g58
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g59
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g60
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g61
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g62
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g63

namespace CKLaneC2R.CompactCover

theorem strip5_m06 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h616 : a ≤ ((127773/128000 : ℚ) : ℝ)
  · -- left
    by_cases h617 : a ≤ ((255447/256000 : ℚ) : ℝ)
    · -- left
      by_cases h618 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s099 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h617 h618
      · -- right
        by_cases h623 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s100 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h617 h618 h623
        · -- right
          by_cases h625 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s101 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h617 h618 h623 h625
          · -- right
            by_cases h627 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s102 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h617 h618 h623 h625 h627
            · -- right
              exact strip5_s103 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h617 h618 h623 h625 h627
    · -- right
      by_cases h642 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s104 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h617 h642
      · -- right
        by_cases h647 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s105 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h617 h642 h647
        · -- right
          by_cases h649 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s106 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h617 h642 h647 h649
          · -- right
            by_cases h651 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s107 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h617 h642 h647 h649 h651
            · -- right
              by_cases h653 : z ≤ ((6211/6400 : ℚ) : ℝ)
              · -- left
                exact strip5_s108 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h617 h642 h647 h649 h651 h653
              · -- right
                exact strip5_s109 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h617 h642 h647 h649 h651 h653
  · -- right
    by_cases h667 : a ≤ ((51129/51200 : ℚ) : ℝ)
    · -- left
      by_cases h668 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s110 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h668
      · -- right
        by_cases h673 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s111 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h668 h673
        · -- right
          by_cases h675 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s112 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h668 h673 h675
          · -- right
            by_cases h677 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s113 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h668 h673 h675 h677
            · -- right
              by_cases h679 : z ≤ ((6211/6400 : ℚ) : ℝ)
              · -- left
                exact strip5_s114 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h668 h673 h675 h677 h679
              · -- right
                by_cases h681 : z ≤ ((63023/64000 : ℚ) : ℝ)
                · -- left
                  exact strip5_s115 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h668 h673 h675 h677 h679 h681
                · -- right
                  exact strip5_s116 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h668 h673 h675 h677 h679 h681
    · -- right
      by_cases h694 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s117 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h694
      · -- right
        by_cases h703 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s118 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h694 h703
        · -- right
          by_cases h706 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s119 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h694 h703 h706
          · -- right
            by_cases h708 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s120 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h694 h703 h706 h708
            · -- right
              by_cases h710 : z ≤ ((6211/6400 : ℚ) : ℝ)
              · -- left
                exact strip5_s121 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h694 h703 h706 h708 h710
              · -- right
                by_cases h713 : z ≤ ((63023/64000 : ℚ) : ℝ)
                · -- left
                  exact strip5_s122 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h694 h703 h706 h708 h710 h713
                · -- right
                  by_cases h716 : z ≤ ((126959/128000 : ℚ) : ℝ)
                  · -- left
                    exact strip5_s123 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h694 h703 h706 h708 h710 h713 h716
                  · -- right
                    exact strip5_s124 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550 h616 h667 h694 h703 h706 h708 h710 h713 h716

end CKLaneC2R.CompactCover


