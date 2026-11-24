-- Prove2me | Definitions.Def_RequestProject_TwoThirdsFull
-- name    : RequestProject_TwoThirdsFull
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:29:34.794684+00:00
-- url     : https://prove2.me/theorems/e1bfe644-a4e5-4fc3-8e62-1f14971c8eb3
-- title:
--   Two Thirds Full
-- statement:
--   Definitions and structural lemmas for Two Thirds Full, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsFull.lean

import Mathlib
import Definitions.Def_RequestProject_TwoThirds
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
end FairSelling


