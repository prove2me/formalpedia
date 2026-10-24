-- Prove2me | Definitions.Def_PricingWithTips3DM_0e75ff46933231ddbfe3b079Part1
-- name    : PricingWithTips3DM_0e75ff46933231ddbfe3b079Part1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:00:17.164134+00:00
-- url     : https://prove2.me/theorems/19e474e3-e764-44ae-b19d-7cf0a471f4c4
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesPriorRows.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_587002a90801ede7195efef5
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Occurrence compatibility edges: all prior rows

This file iterates the verified one-row scan across the complete family below
one current occurrence.  The resulting reversed rows carry their exact
compatibility tags and the controller reaches the counter-cleanup boundary.
-/

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- One reversed prior row together with its compatibility tag. -/
def encodeTaggedOccurrenceEntry
    (current prior : IndexedOccurrence × Nat) : List UnaryFrameSym :=
  encodeCompatibilityTag (indexedOccurrencesCompatibleCode current prior) ++
    (encodeIndexedOccurrenceEntry prior).reverse
end TMClique
end Turing
end Chapter34
end CLRS


