-- Prove2me | Definitions.Def_GrahamPollak_Solution
-- name    : GrahamPollak_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:15:06.885838+00:00
-- url     : https://prove2.me/theorems/419c3ec5-c5d9-5dad-80f5-2d0f73e63082
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/graham-pollak; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Graham-Pollak theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/graham-pollak/blob/68d32f0faf102fc1716ac89ffc861eefe897e749/Solution.lean

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GrahamPollakTheorem
variable {V : Type*}
def IsBicliqueDecomposition [DecidableEq V] {m : ℕ} (A B : Fin m → Finset V) : Prop :=
  (∀ i, Disjoint (A i) (B i)) ∧
    ∀ u v : V, u ≠ v →
      (Finset.univ.filter (fun i => (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i))).card = 1
end GrahamPollakTheorem


