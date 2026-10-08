-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m05
-- name    : CK_CKLaneC2R_CompactCover_S01_m05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T17:56:33.103644+00:00
-- url     : https://prove2.me/theorems/4cea8947-021d-4dfb-9a7e-6f4444ffdb0c
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g41
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g42
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g43
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g44
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g45

namespace CKLaneC2R.CompactCover

theorem strip1_m05 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : ¬ (a ≤ ((37/160 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h513 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h514 : z ≤ ((1257/4000 : ℚ) : ℝ)
    · -- left
      by_cases h515 : z ≤ ((1601/8000 : ℚ) : ℝ)
      · -- left
        by_cases h516 : a ≤ ((15/64 : ℚ) : ℝ)
        · -- left
          exact strip1_s052 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h513 h514 h515 h516
        · -- right
          exact strip1_s053 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h513 h514 h515 h516
      · -- right
        exact strip1_s054 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h513 h514 h515
    · -- right
      exact strip1_s055 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h513 h514
  · -- right
    by_cases h561 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip1_s056 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h513 h561
    · -- right
      by_cases h573 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip1_s057 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h513 h561 h573
      · -- right
        by_cases h581 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip1_s058 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h513 h561 h573 h581
        · -- right
          exact strip1_s059 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h513 h561 h573 h581

end CKLaneC2R.CompactCover


