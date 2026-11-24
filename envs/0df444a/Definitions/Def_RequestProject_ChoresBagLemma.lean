-- Prove2me | Definitions.Def_RequestProject_ChoresBagLemma
-- name    : RequestProject_ChoresBagLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:00.363966+00:00
-- url     : https://prove2.me/theorems/01a5c0f7-4bda-424c-b81b-75a8a07a4d23
-- title:
--   Chores Bag Lemma
-- statement:
--   Definitions and structural lemmas for Chores Bag Lemma, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagLemma.lean

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
namespace FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable (c : Fin n → T → ℝ) (p : T → ℝ) (mu : Fin n → ℝ)
def BagGoal (A : Finset (Fin n)) (R : Finset T) : Prop :=
  (∀ i ∈ A, ∀ t ∈ R, 2 * mu i < cbar (c i) p t) ∨
  ∃ B ⊆ R, B.Nonempty ∧ ∃ i ∈ A, cbarSum (c i) p B ≤ 2 * mu i ∧
    ∀ j ∈ A, j ≠ i → (mu j ≤ cbarSum (c j) p B ∨ ∀ t ∈ R \ B, mu j < cbar (c j) p t)
variable {c p mu}
end FairChores


