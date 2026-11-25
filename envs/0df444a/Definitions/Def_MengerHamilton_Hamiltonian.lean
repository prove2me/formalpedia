-- Prove2me | Definitions.Def_MengerHamilton_Hamiltonian
-- name    : MengerHamilton_Hamiltonian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:15:36.176485+00:00
-- url     : https://prove2.me/theorems/a30b94bc-f194-40ba-9545-98d5eb1ac3c1
-- title:
--   Hamiltonian
-- statement:
--   Definitions and structural lemmas for Hamiltonian, from Juan Pablo Traverso Gianini (jtraverso/chvatal-posa-hamiltonian; see pinned Apache-2.0 LICENSE and source headers)'s pinned Chvatal's and Posa's degree conditions for Hamiltonian cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Hamiltonian.lean

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_ClosureAux
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace Hamiltonicity
variable {V : Type*}
def IsKConnected [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected
end Hamiltonicity


