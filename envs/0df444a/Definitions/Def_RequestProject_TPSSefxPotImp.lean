-- Prove2me | Definitions.Def_RequestProject_TPSSefxPotImp
-- name    : RequestProject_TPSSefxPotImp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:22:11.433741+00:00
-- url     : https://prove2.me/theorems/dec38ce7-38b3-495f-8cb3-1c8aa35a87aa
-- title:
--   TPSSefx Pot Imp
-- statement:
--   Definitions and structural lemmas for TPSSefx Pot Imp, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotImp.lean

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPotStep
import Definitions.Def_RequestProject_TPSSefxStep
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
section Step
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
end Step
end PotTPS
end FairSelling


