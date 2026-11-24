-- Prove2me | Definitions.Def_RequestProject_TPSSefxTheorem2
-- name    : RequestProject_TPSSefxTheorem2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:28:52.331138+00:00
-- url     : https://prove2.me/theorems/4e9fdd1c-750e-4e0e-b000-30d2b741f282
-- title:
--   TPSSefx Theorem2
-- statement:
--   Definitions and structural lemmas for TPSSefx Theorem2, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxTheorem2.lean

import Mathlib
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxPotImp
import Definitions.Def_RequestProject_TPSApprox
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace ChargeTPS
end ChargeTPS
end FairSelling


