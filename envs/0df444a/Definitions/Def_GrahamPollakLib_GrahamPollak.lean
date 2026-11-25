-- Prove2me | Definitions.Def_GrahamPollakLib_GrahamPollak
-- name    : GrahamPollakLib_GrahamPollak
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:12:49.205637+00:00
-- url     : https://prove2.me/theorems/490df493-b492-5cbd-9828-00f7a9900f1c
-- title:
--   Graham Pollak
-- statement:
--   Definitions and structural lemmas for Graham Pollak, from Juan Pablo Traverso Gianini (jtraverso/graham-pollak; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Graham-Pollak theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/GrahamPollakLib/GrahamPollak.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GrahamPollak
variable {V : Type*}
def IsBicliqueDecomposition [DecidableEq V] {m : ℕ} (A B : Fin m → Finset V) : Prop :=
  (∀ i, Disjoint (A i) (B i)) ∧
    ∀ u v : V, u ≠ v →
      (Finset.univ.filter (fun i => (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i))).card = 1
section Aux
variable [DecidableEq V]
end Aux
end GrahamPollak


