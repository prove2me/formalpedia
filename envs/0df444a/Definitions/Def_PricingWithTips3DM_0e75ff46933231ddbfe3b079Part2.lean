-- Prove2me | Definitions.Def_PricingWithTips3DM_0e75ff46933231ddbfe3b079Part2
-- name    : PricingWithTips3DM_0e75ff46933231ddbfe3b079Part2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:05:28.834415+00:00
-- url     : https://prove2.me/theorems/9d453850-6cff-4858-91b6-9c7731b158ae
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesPriorRows.Part2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_0e75ff46933231ddbfe3b079Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Tagged physical family used by the restoration and emission phases. -/
def encodeTaggedOccurrenceEntries
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : List UnaryFrameSym :=
  priors.flatMap (encodeTaggedOccurrenceEntry current)
end TMClique
end Turing
end Chapter34
end CLRS


