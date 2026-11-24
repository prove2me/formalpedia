-- Prove2me | Definitions.Def_RequestProject_TwoAgents
-- name    : RequestProject_TwoAgents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:46.465556+00:00
-- url     : https://prove2.me/theorems/631c06dc-f8f0-4fa9-b872-91126f039209
-- title:
--   Two Agents
-- statement:
--   Definitions and structural lemmas for Two Agents, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean

import Mathlib
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
def Config (w p : G → ℝ) (r : ℝ) (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ) : Prop :=
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint s (A i)) ∧
  (s ∪ Finset.univ.biUnion A = Finset.univ) ∧ (∀ i, 0 ≤ q i) ∧
  (∑ i, q i = ∑ g ∈ s, p g) ∧ (∀ i, r ≤ vbarSum w p (A i) + q i)
def swapOutcome (o : Outcome G 2) : Outcome G 2 where
  sold := o.sold
  kept := fun i => o.kept (Equiv.swap 0 1 i)
  money := fun i => o.money (Equiv.swap 0 1 i)
end FairSelling


