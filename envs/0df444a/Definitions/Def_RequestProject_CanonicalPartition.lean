-- Prove2me | Definitions.Def_RequestProject_CanonicalPartition
-- name    : RequestProject_CanonicalPartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:13:16.778927+00:00
-- url     : https://prove2.me/theorems/3a5760b7-be96-490a-a74e-47f481f7fad4
-- title:
--   Canonical Partition
-- statement:
--   Definitions and structural lemmas for Canonical Partition, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalPartition.lean

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_MMSPartition
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
def IsCanonical (w p : G → ℝ) (τ : ℝ) (kept : Fin 3 → Finset G) (sold : Finset G)
    (money : Fin 3 → ℝ) (leftover : Fin 3) : Prop :=
  (∀ j k, j ≠ k → Disjoint (kept j) (kept k)) ∧
  (∀ k, Disjoint sold (kept k)) ∧
  (∀ k, 0 ≤ money k) ∧
  (∑ k, money k ≤ ∑ g ∈ sold, p g) ∧
  (∀ k, τ ≤ vbarSum w p (kept k) + money k) ∧
  (∀ k, k ≠ leftover → money k = 0 ∨ (kept k).card = 1)
end FairSelling


