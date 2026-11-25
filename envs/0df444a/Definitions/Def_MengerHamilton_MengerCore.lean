-- Prove2me | Definitions.Def_MengerHamilton_MengerCore
-- name    : MengerHamilton_MengerCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:07:14.757976+00:00
-- url     : https://prove2.me/theorems/4aa9deb1-640f-499a-8fb0-bd31a2562dd1
-- title:
--   Menger Core
-- statement:
--   Definitions and structural lemmas for Menger Core, from Juan Pablo Traverso Gianini (jtraverso/chvatal-posa-hamiltonian; see pinned Apache-2.0 LICENSE and source headers)'s pinned Chvatal's and Posa's degree conditions for Hamiltonian cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace Menger.Aux
variable {V : Type*}
def Sep (G : SimpleGraph V) (A B X : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ x ∈ X, x ∈ p.support
def R (H : SimpleGraph V) (A Y : Finset V) (w : V) : Prop :=
  ∃ a ∈ A, ∃ p : H.Walk a w, ∀ u ∈ p.support, u ∉ Y
def Fam (G : SimpleGraph V) (A B : Finset V) (k : ℕ) : Prop :=
  ∃ P : Fin k → Σ a b : V, G.Walk a b,
    (∀ i, (P i).1 ∈ A ∧ (P i).2.1 ∈ B ∧ (P i).2.2.IsPath ∧
      (∀ w ∈ (P i).2.2.support, w ∈ A → w = (P i).1) ∧
      (∀ w ∈ (P i).2.2.support, w ∈ B → w = (P i).2.1)) ∧
    ∀ i j, i ≠ j → ∀ w ∈ (P i).2.2.support, w ∉ (P j).2.2.support
end Menger.Aux


