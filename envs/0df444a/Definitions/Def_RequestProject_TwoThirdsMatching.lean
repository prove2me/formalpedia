-- Prove2me | Definitions.Def_RequestProject_TwoThirdsMatching
-- name    : RequestProject_TwoThirdsMatching
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:20.359794+00:00
-- url     : https://prove2.me/theorems/154b79f9-937f-447e-beef-676052742a30
-- title:
--   Two Thirds Matching
-- statement:
--   Definitions and structural lemmas for Two Thirds Matching, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsMatching.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
def nbhd (B : Finset β) (acc : α → β → Prop) [DecidableRel acc] (a : α) : Finset β :=
  B.filter (fun b => acc a b)
end FairSelling


