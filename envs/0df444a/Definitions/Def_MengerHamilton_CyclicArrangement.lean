-- Prove2me | Definitions.Def_MengerHamilton_CyclicArrangement
-- name    : MengerHamilton_CyclicArrangement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:11:23.967496+00:00
-- url     : https://prove2.me/theorems/e647cee8-5b89-5302-acc6-521d42c46278
-- title:
--   Cyclic Arrangement
-- statement:
--   Definitions and structural lemmas for Cyclic Arrangement, from Juan Pablo Traverso Gianini (jtraverso/chvatal-posa-hamiltonian; see pinned Apache-2.0 LICENSE and source headers)'s pinned Chvatal's and Posa's degree conditions for Hamiltonian cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean

module
public import Definitions.Def_MengerHamilton_Menger
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace Hamiltonicity
variable {V : Type*}
structure CycArr (G : SimpleGraph V) (m : ℕ) (f : ℕ → V) : Prop where
  three_le : 3 ≤ m
  periodic : ∀ i, f (i + m) = f i
  inj : ∀ i j, i < m → j < m → f i = f j → i = j
  adj : ∀ i, G.Adj (f i) (f (i + 1))
namespace CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
end CycArr
def walkOf (G : SimpleGraph V) (f : ℕ → V) (hf : ∀ i, G.Adj (f i) (f (i + 1))) :
    (n : ℕ) → G.Walk (f 0) (f n)
  | 0 => Walk.nil
  | n + 1 => (walkOf G f hf n).concat (hf n)
namespace CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
end CycArr
end Hamiltonicity


