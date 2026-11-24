-- Prove2me | Definitions.Def_RequestProject_TPSSefxPotStep
-- name    : RequestProject_TPSSefxPotStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:21:02.175895+00:00
-- url     : https://prove2.me/theorems/a940df12-6240-4c08-bf46-8b13d76f30a4
-- title:
--   TPSSefx Pot Step
-- statement:
--   Definitions and structural lemmas for TPSSefx Pot Step, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotStep.lean

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPot
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
end PotTPS
end FairSelling


