-- Prove2me | Definitions.Def_RequestProject_TwoThirdsBagFilling
-- name    : RequestProject_TwoThirdsBagFilling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:21.340808+00:00
-- url     : https://prove2.me/theorems/494968f7-cb8c-4910-b792-758c87a68a8b
-- title:
--   Two Thirds Bag Filling
-- statement:
--   Definitions and structural lemmas for Two Thirds Bag Filling, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBagFilling.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [DecidableEq G]
end FairSelling


