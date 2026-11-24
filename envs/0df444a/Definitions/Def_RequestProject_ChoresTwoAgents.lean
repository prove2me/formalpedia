-- Prove2me | Definitions.Def_RequestProject_ChoresTwoAgents
-- name    : RequestProject_ChoresTwoAgents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:51.186325+00:00
-- url     : https://prove2.me/theorems/2959fda0-a240-4973-ac7d-0c494e8e21ea
-- title:
--   Chores Two Agents
-- statement:
--   Definitions and structural lemmas for Chores Two Agents, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
set_option autoImplicit true
open scoped BigOperators
namespace FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
def ConfigC (c p : T → ℝ) (r : ℝ) (A : Fin 2 → Finset T) (s : Finset T) (q : Fin 2 → ℝ) :
    Prop :=
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint s (A i)) ∧
  (s ∪ Finset.univ.biUnion A = Finset.univ) ∧ (∀ i, 0 ≤ q i) ∧
  (∑ i, q i = ∑ t ∈ s, p t) ∧ (∀ i, cbarSum c p (A i) + q i ≤ r)
def swapOutcomeC (o : Outcome T 2) : Outcome T 2 where
  outsourced := o.outsourced
  kept := fun i => o.kept (Equiv.swap 0 1 i)
  pay := fun i => o.pay (Equiv.swap 0 1 i)
end FairChores


