-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapBatchJointOwnerAdapter
-- name    : CK_GeneralCK_PureGapDoubleCapBatchJointOwnerAdapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:01:12.146271+00:00
-- url     : https://prove2.me/theorems/79e5ce6b-0c9b-4c96-ae91-db549ab7a8ee
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapBatchJointOwnerAdapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapBatchJointOwnerAdapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapBatchJointOwnerAdapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapBatchJointOwnerAdapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapBatchJointOwnerAdapter.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowFirstFifthAssembly
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_All
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailNearZeroOwnerAdapter

-- ===== source module GeneralCK.PureGapDoubleCapBatchJointOwnerAdapter =====
section

/-!
The three sealed cell batches join at the exact closed endpoints
`1/5`, `1/4`, and `2/5`. This module is source-only until all 228 low-middle,
480 compact-middle, and 256 high-middle cell receipts and their aggregations
pass direct named Lean audits. In particular, a generated source or a numerical
preflight does not discharge any premise here.
-/

namespace GeneralCK

theorem doubleCapRemainingRegionsV26_of_joint_batches :
    DoubleCapRemainingRegionsV26 := by
  constructor
  · intro m hm100 hmQuarter
    by_cases hmFifth : m ≤ 1 / 5
    · exact doubleCapLowResidual_nonneg_first_fifth
        (by linarith) hmFifth
    · exact Certificates.DoubleCapMiddle.doubleCapMiddleAggregation.1
        m (by linarith) hmQuarter
  · intro m hmQuarter hmSeven
    by_cases hmTwoFifths : m ≤ 2 / 5
    · exact Certificates.DoubleCapMiddle.doubleCapMiddleAggregation.2
        m hmQuarter.le hmTwoFifths
    · exact Certificates.DoubleCapHighMiddleDerivative.bridgeValueResidual_nonneg
        (by linarith) hmSeven.le

theorem canonicalDoubleCapEntropyEndpoints_of_joint_batches :
    CanonicalDoubleCapEntropyEndpoints :=
  DoubleCapRemainingRegionsV26.toEndpoints
    doubleCapRemainingRegionsV26_of_joint_batches

#print axioms doubleCapRemainingRegionsV26_of_joint_batches
#print axioms canonicalDoubleCapEntropyEndpoints_of_joint_batches

end GeneralCK

end


