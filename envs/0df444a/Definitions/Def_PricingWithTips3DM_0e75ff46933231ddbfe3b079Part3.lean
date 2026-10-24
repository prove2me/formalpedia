-- Prove2me | Definitions.Def_PricingWithTips3DM_0e75ff46933231ddbfe3b079Part3
-- name    : PricingWithTips3DM_0e75ff46933231ddbfe3b079Part3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:08:11.174524+00:00
-- url     : https://prove2.me/theorems/08ecb02a-fe5f-4afe-ae3d-a452a09bed66
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesPriorRows.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_0e75ff46933231ddbfe3b079Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Exact accumulated budget for scanning every row below one current row. -/
def compatibilityEdgesPriorRowsSteps
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : Nat :=
  (priors.map (compatibilityEdgesPriorRowSteps current)).sum
end TMClique
end Turing
end Chapter34
end CLRS


