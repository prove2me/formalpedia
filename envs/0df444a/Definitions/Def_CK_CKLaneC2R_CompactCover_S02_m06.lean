-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m06
-- name    : CK_CKLaneC2R_CompactCover_S02_m06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T16:33:03.223998+00:00
-- url     : https://prove2.me/theorems/d71d4a73-9b68-432b-847a-b16a72cbd8af
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g40
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g41
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g42
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g43
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g44
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g45

namespace CKLaneC2R.CompactCover

theorem strip2_m06 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : ¬ (a ≤ ((17/40 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h630 : a ≤ ((7/16 : ℚ) : ℝ)
  · -- left
    by_cases h631 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h632 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        exact strip2_s060 ha1 ha2 hz1 hz2 h0 h534 h535 h630 h631 h632
      · -- right
        exact strip2_s061 ha1 ha2 hz1 hz2 h0 h534 h535 h630 h631 h632
    · -- right
      by_cases h653 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip2_s062 ha1 ha2 hz1 hz2 h0 h534 h535 h630 h631 h653
      · -- right
        exact strip2_s063 ha1 ha2 hz1 hz2 h0 h534 h535 h630 h631 h653
  · -- right
    by_cases h675 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h676 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        exact strip2_s064 ha1 ha2 hz1 hz2 h0 h534 h535 h630 h675 h676
      · -- right
        exact strip2_s065 ha1 ha2 hz1 hz2 h0 h534 h535 h630 h675 h676
    · -- right
      by_cases h696 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip2_s066 ha1 ha2 hz1 hz2 h0 h534 h535 h630 h675 h696
      · -- right
        exact strip2_s067 ha1 ha2 hz1 hz2 h0 h534 h535 h630 h675 h696

end CKLaneC2R.CompactCover


