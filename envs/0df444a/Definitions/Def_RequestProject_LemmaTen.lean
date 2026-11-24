-- Prove2me | Definitions.Def_RequestProject_LemmaTen
-- name    : RequestProject_LemmaTen
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:53.754973+00:00
-- url     : https://prove2.me/theorems/802740f8-d910-4dc2-bcc1-aea0d1390d3e
-- title:
--   Lemma Ten
-- statement:
--   Definitions and structural lemmas for Lemma Ten, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
def Outcome.AllocatesAll (o : Outcome G n) : Prop :=
  o.sold ∪ Finset.univ.biUnion o.kept = Finset.univ
def Outcome.Full (p : G → ℝ) (sellable : Finset G) (o : Outcome G n) : Prop :=
  o.Valid p ∧ o.sold ⊆ sellable ∧ o.AllocatesAll ∧ ∑ j, o.money j = ∑ g ∈ o.sold, p g
def IsPartitionOf (A : Fin n → Finset G) (T : Finset G) : Prop :=
  (∀ j k, j ≠ k → Disjoint (A j) (A k)) ∧ Finset.univ.biUnion A = T
def EFXalloc (v : Fin n → G → ℝ) (A : Fin n → Finset G) : Prop :=
  ∀ i j, ∀ g ∈ A j, ∑ g' ∈ A i, v i g' ≥ ∑ g' ∈ A j \ {g}, v i g'
def EF1alloc (v : Fin n → G → ℝ) (A : Fin n → Finset G) : Prop :=
  ∀ i j, (A j).Nonempty → ∃ g ∈ A j, ∑ g' ∈ A i, v i g' ≥ ∑ g' ∈ A j \ {g}, v i g'
section EFXtoSEFX
variable (v : Fin n → G → ℝ) (p : G → ℝ) (sellable : Finset G) (A : Fin n → Finset G)
def sellAllOutcome (P : Fin n → ℝ) : Outcome G n := ⟨sellable, A, P⟩
variable {v p sellable A}
end EFXtoSEFX
end FairSelling


