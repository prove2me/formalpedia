-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowFirstFifthAssembly
-- name    : CK_GeneralCK_PureGapDoubleCapLowFirstFifthAssembly
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:03:12.843233+00:00
-- url     : https://prove2.me/theorems/8126a8a5-63ef-4d71-9227-08dc8def84da
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowFirstFifthAssembly` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowFirstFifthAssembly` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowFirstFifthAssembly` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowFirstFifthAssembly (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowFirstFifthAssembly.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailActualSign
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_All

-- ===== source module GeneralCK.PureGapDoubleCapLowFirstFifthAssembly =====
section

/-! The checked near-zero tail and the sealed low-middle cell aggregation
join on the closed endpoint `1/100`. This source becomes an accepted owner
only after all 228 cells and the split aggregation pass named Lean audits. -/

namespace GeneralCK

theorem doubleCapLowResidual_nonneg_first_fifth {m : ℝ}
    (hm : 0 < m) (hm5 : m ≤ 1 / 5) :
    0 ≤ doubleCapLowResidual m := by
  by_cases hm100 : m ≤ 1 / 100
  · exact doubleCapLowResidual_nonneg_near_zero hm hm100
  · exact Certificates.DoubleCapLowMiddleAggregation.doubleCapLowMiddleAggregation
      m (by linarith [lt_of_not_ge hm100]) hm5

#print axioms doubleCapLowResidual_nonneg_first_fifth

end GeneralCK

end


