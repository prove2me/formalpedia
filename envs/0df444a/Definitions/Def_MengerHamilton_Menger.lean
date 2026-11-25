-- Prove2me | Definitions.Def_MengerHamilton_Menger
-- name    : MengerHamilton_Menger
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:08:56.008914+00:00
-- url     : https://prove2.me/theorems/551b64ee-d927-57f4-84e8-6f004f4536bf
-- title:
--   Menger
-- statement:
--   Definitions and structural lemmas for Menger, from Juan Pablo Traverso Gianini (jtraverso/chvatal-posa-hamiltonian; see pinned Apache-2.0 LICENSE and source headers)'s pinned Chvatal's and Posa's degree conditions for Hamiltonian cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Menger.lean

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace Menger
variable {V : Type*}
def Separates (G : SimpleGraph V) (A B X : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ x ∈ X, x ∈ p.support
end Menger


