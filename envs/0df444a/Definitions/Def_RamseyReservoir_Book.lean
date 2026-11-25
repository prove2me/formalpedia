-- Prove2me | Definitions.Def_RamseyReservoir_Book
-- name    : RamseyReservoir_Book
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:28:30.759833+00:00
-- url     : https://prove2.me/theorems/c29247ef-5943-5c5c-a1b0-aa51d76677a3
-- title:
--   Book
-- statement:
--   Definitions and structural lemmas for Book, from Brian Sanders (Egly443/lean-ramsey-reservoir; see pinned Apache-2.0 LICENSE and source headers)'s pinned Reservoir and book calculus for greedy Ramsey arguments development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
def ContainsBook (G : SimpleGraph V) (m t : ℕ) : Prop :=
  ∃ R : G.Reservoir, #R.spine = m ∧ t ≤ #R.pool
variable [Fintype V] [DecidableRel G.Adj]
def orderedTriangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V × V) :=
  {x | G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2}
end SimpleGraph


