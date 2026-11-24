-- Prove2me | Definitions.Def_RequestProject_ChoresBagFilling
-- name    : RequestProject_ChoresBagFilling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:11:39.244393+00:00
-- url     : https://prove2.me/theorems/c4bd2594-448d-4ab3-8353-58c6c395bf26
-- title:
--   Chores Bag Filling
-- statement:
--   Definitions and structural lemmas for Chores Bag Filling, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagFilling.lean

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresBagLemma
set_option autoImplicit true
open scoped BigOperators
namespace FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
def Inv (c : Fin n → T → ℝ) (p : T → ℝ) (mu : Fin n → ℝ) (i : Fin n) (k : ℕ)
    (R : Finset T) : Prop :=
  (wtSum (c i) p (mu i) R ≤ k * mu i) ∨
  (wtSum (c i) p (mu i) R ≤ (k + 1) * mu i ∧ ∀ t ∈ R, mu i < cbar (c i) p t)
variable {c : Fin n → T → ℝ} {p : T → ℝ} {mu : Fin n → ℝ}
end FairChores


