-- Prove2me | Definitions.Def_RequestProject_ThreeAgentCashComposition
-- name    : RequestProject_ThreeAgentCashComposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:14:09.213851+00:00
-- url     : https://prove2.me/theorems/e3eef627-7a81-41c7-aa51-c00da949bbef
-- title:
--   Three Agent Cash Composition
-- statement:
--   Definitions and structural lemmas for Three Agent Cash Composition, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
def optionGoods (s : Finset (Option G)) : Finset G :=
  s.biUnion (fun x => match x with | none => ∅ | some g => {g})
def dropCashOutcome (o : Outcome (Option G) 2) : Outcome G 2 where
  sold := optionGoods o.sold
  kept i := optionGoods (o.kept i)
  money := o.money
end FairSelling


