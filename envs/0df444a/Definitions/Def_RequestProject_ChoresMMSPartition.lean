-- Prove2me | Definitions.Def_RequestProject_ChoresMMSPartition
-- name    : RequestProject_ChoresMMSPartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:13.87892+00:00
-- url     : https://prove2.me/theorems/670b3140-e446-4b69-b9b4-4591a7fae57a
-- title:
--   Chores MMSPartition
-- statement:
--   Definitions and structural lemmas for Chores MMSPartition, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
namespace FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
noncomputable def maxCost (c : T → ℝ) (o : Outcome T n) : ℝ := ⨆ j, cost c o j
def assignOutcome (assign : T → Option (Fin n)) (m : Fin n → ℝ) : Outcome T n where
  outsourced := Finset.univ.filter (fun t => assign t = none)
  kept := fun j => Finset.univ.filter (fun t => assign t = some j)
  pay := m
noncomputable def billOf (p : T → ℝ) (assign : T → Option (Fin n)) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => assign t = none), p t
noncomputable def keptCost (c : T → ℝ) (assign : T → Option (Fin n)) (j : Fin n) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => assign t = some j), c t
noncomputable def maxCostData (c : T → ℝ) (assign : T → Option (Fin n)) (m : Fin n → ℝ) : ℝ :=
  ⨆ j, keptCost c assign j + m j
end FairChores


