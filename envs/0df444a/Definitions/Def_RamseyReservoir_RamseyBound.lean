-- Prove2me | Definitions.Def_RamseyReservoir_RamseyBound
-- name    : RamseyReservoir_RamseyBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:25:14.395503+00:00
-- url     : https://prove2.me/theorems/7c6077a7-3721-4ee0-85c2-454322cdc80b
-- title:
--   Ramsey Bound
-- statement:
--   Definitions and structural lemmas for Ramsey Bound, from Brian Sanders (Egly443/lean-ramsey-reservoir; see pinned Apache-2.0 LICENSE and source headers)'s pinned Reservoir and book calculus for greedy Ramsey arguments development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace SimpleGraph
def RamseyBound (n r s : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), (∃ t, G.IsNClique r t) ∨ ∃ t, Gᶜ.IsNClique s t
variable {V : Type*} {n m r s : ℕ}
end SimpleGraph


