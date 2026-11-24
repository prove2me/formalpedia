-- Prove2me | Definitions.Def_RequestProject_MMSPartition
-- name    : RequestProject_MMSPartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:11:36.120811+00:00
-- url     : https://prove2.me/theorems/a6126326-a181-4a54-8c59-0fd88e75ced2
-- title:
--   MMSPartition
-- statement:
--   Definitions and structural lemmas for MMSPartition, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MMSPartition.lean

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
def ConfigN (n : ℕ) (w p : G → ℝ) (r : ℝ) (A : Fin n → Finset G) (s : Finset G) (q : Fin n → ℝ) :
    Prop :=
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint s (A i)) ∧
  (s ∪ Finset.univ.biUnion A = Finset.univ) ∧ (∀ i, 0 ≤ q i) ∧
  (∑ i, q i = ∑ g ∈ s, p g) ∧ (∀ i, r ≤ vbarSum w p (A i) + q i)
end FairSelling


