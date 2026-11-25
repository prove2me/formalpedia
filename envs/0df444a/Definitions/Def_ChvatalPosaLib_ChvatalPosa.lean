-- Prove2me | Definitions.Def_ChvatalPosaLib_ChvatalPosa
-- name    : ChvatalPosaLib_ChvatalPosa
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:16:58.950881+00:00
-- url     : https://prove2.me/theorems/2d588608-345e-4489-8473-00173ec29076
-- title:
--   Chvatal Posa
-- statement:
--   Definitions and structural lemmas for Chvatal Posa, from Juan Pablo Traverso Gianini (jtraverso/chvatal-posa-hamiltonian; see pinned Apache-2.0 LICENSE and source headers)'s pinned Chvatal's and Posa's degree conditions for Hamiltonian cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/ChvatalPosaLib/ChvatalPosa.lean

module
public import Mathlib
public import Definitions.Def_MengerHamilton_Hamiltonian
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace ChvatalPosa
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def ChvatalCond (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  ∀ i : ℕ, 1 ≤ i → 2 * i < Fintype.card V →
    i ≤ #{v | H.degree v ≤ i} → i + 1 ≤ #{v | Fintype.card V - i ≤ H.degree v}
end ChvatalPosa


