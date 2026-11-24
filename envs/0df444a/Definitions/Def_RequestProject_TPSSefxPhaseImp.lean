-- Prove2me | Definitions.Def_RequestProject_TPSSefxPhaseImp
-- name    : RequestProject_TPSSefxPhaseImp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:21:52.231928+00:00
-- url     : https://prove2.me/theorems/eed204cb-6e2a-40a6-b1c8-1acd7a132499
-- title:
--   TPSSefx Phase Imp
-- statement:
--   Definitions and structural lemmas for TPSSefx Phase Imp, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Definitions.Def_RequestProject_TPSSefxStep
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
section Step
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
end Step
end PhaseTPS
end FairSelling


