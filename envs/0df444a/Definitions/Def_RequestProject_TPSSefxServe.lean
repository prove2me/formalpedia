-- Prove2me | Definitions.Def_RequestProject_TPSSefxServe
-- name    : RequestProject_TPSSefxServe
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:17:01.122792+00:00
-- url     : https://prove2.me/theorems/f85e8243-4e88-4ef8-b3f5-b8a675ceccf2
-- title:
--   TPSSefx Serve
-- statement:
--   Definitions and structural lemmas for TPSSefx Serve, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace CStage
end CStage
end ChargeTPS
end FairSelling


