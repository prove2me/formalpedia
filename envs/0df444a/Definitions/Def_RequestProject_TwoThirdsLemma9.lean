-- Prove2me | Definitions.Def_RequestProject_TwoThirdsLemma9
-- name    : RequestProject_TwoThirdsLemma9
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:17:27.336736+00:00
-- url     : https://prove2.me/theorems/1ef8d291-db45-4e06-9498-ef2a2f6ae7a3
-- title:
--   Two Thirds Lemma9
-- statement:
--   Definitions and structural lemmas for Two Thirds Lemma9, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLemma9.lean

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsBudget
import Definitions.Def_RequestProject_TwoThirdsDescent
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
end FairSelling


