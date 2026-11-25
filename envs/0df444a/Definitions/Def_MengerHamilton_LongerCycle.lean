-- Prove2me | Definitions.Def_MengerHamilton_LongerCycle
-- name    : MengerHamilton_LongerCycle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:12:38.914603+00:00
-- url     : https://prove2.me/theorems/ea13441f-d28a-50a3-a438-8ed085498b8a
-- title:
--   Longer Cycle
-- statement:
--   Definitions and structural lemmas for Longer Cycle, from Juan Pablo Traverso Gianini (jtraverso/chvatal-posa-hamiltonian; see pinned Apache-2.0 LICENSE and source headers)'s pinned Chvatal's and Posa's degree conditions for Hamiltonian cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/LongerCycle.lean

module
public import Definitions.Def_MengerHamilton_CyclicArrangement
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace Hamiltonicity
variable {V : Type*}
namespace CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
end CycArr
end Hamiltonicity


