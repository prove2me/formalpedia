-- Prove2me | Definitions.Def_RequestProject_ChoresPreAlloc
-- name    : RequestProject_ChoresPreAlloc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:50.939062+00:00
-- url     : https://prove2.me/theorems/89ac3ad3-7df6-424c-b1d2-8f788fff13d2
-- title:
--   Chores Pre Alloc
-- statement:
--   Definitions and structural lemmas for Chores Pre Alloc, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresPreAlloc.lean

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
namespace FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
structure PreAlloc (T : Type*) (n : ℕ) where
  /-- The bundle handed to each agent. -/
  bundle : Fin n → Finset T
  /-- The chores outsourced collectively. -/
  outs : Finset T
  /-- The share of the collective outsourcing bill paid by each agent. -/
  share : Fin n → ℝ
def PreAlloc.Splits (P : PreAlloc T n) (p : T → ℝ) (A : Finset (Fin n)) (R : Finset T) : Prop :=
  (∀ i ∉ A, P.bundle i = ∅) ∧ (∀ i ∉ A, P.share i = 0) ∧ (∀ i, 0 ≤ P.share i) ∧
  (∀ i j, i ≠ j → Disjoint (P.bundle i) (P.bundle j)) ∧
  (∀ i, Disjoint P.outs (P.bundle i)) ∧
  (P.outs ∪ Finset.univ.biUnion P.bundle = R) ∧
  (∑ i, P.share i = ∑ t ∈ P.outs, p t)
end FairChores


