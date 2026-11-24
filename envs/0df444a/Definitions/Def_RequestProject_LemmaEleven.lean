-- Prove2me | Definitions.Def_RequestProject_LemmaEleven
-- name    : RequestProject_LemmaEleven
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:38.668289+00:00
-- url     : https://prove2.me/theorems/16c1c85b-c93a-43d7-a348-4d1459583697
-- title:
--   Lemma Eleven
-- statement:
--   Definitions and structural lemmas for Lemma Eleven, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open Filter Topology
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
end FairSelling


