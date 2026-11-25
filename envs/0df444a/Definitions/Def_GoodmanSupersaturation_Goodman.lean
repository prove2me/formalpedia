-- Prove2me | Definitions.Def_GoodmanSupersaturation_Goodman
-- name    : GoodmanSupersaturation_Goodman
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:24:18.236025+00:00
-- url     : https://prove2.me/theorems/bbda4425-d995-524e-950e-809a7c439752
-- title:
--   Goodman
-- statement:
--   Definitions and structural lemmas for Goodman, from Brian Sanders (Egly443/lean-goodman-supersaturation; see pinned Apache-2.0 LICENSE and source headers)'s pinned Goodman's formula and supersaturation for two-colourings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def degreeWithin (S : Finset V) (v : V) : ℕ := #{w ∈ S | G.Adj v w}
def cliqueCountIn (S : Finset V) (k : ℕ) : ℕ :=
  #((S.powersetCard k).filter fun T : Finset V => G.IsClique (T : Set V))
def distinctTriples (S : Finset V) : Finset (V × V × V) :=
  {x ∈ S ×ˢ S ×ˢ S | x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2}
def triangleTriples (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) :
    Finset (V × V × V) :=
  {x ∈ S ×ˢ S ×ˢ S | H.Adj x.1 x.2.1 ∧ H.Adj x.1 x.2.2 ∧ H.Adj x.2.1 x.2.2}
def mixedTriples (S : Finset V) : Finset (V × V × V) :=
  {x ∈ S ×ˢ S ×ˢ S | G.Adj x.1 x.2.1 ∧ Gᶜ.Adj x.1 x.2.2}
def mixedInd (x : V × V × V) : ℕ := if G.Adj x.1 x.2.1 ∧ Gᶜ.Adj x.1 x.2.2 then 1 else 0
def monoInd (x : V × V × V) : ℕ :=
  (if G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2 then 1 else 0) +
    if Gᶜ.Adj x.1 x.2.1 ∧ Gᶜ.Adj x.1 x.2.2 ∧ Gᶜ.Adj x.2.1 x.2.2 then 1 else 0
section Fintype
variable [Fintype V]
end Fintype
end SimpleGraph


