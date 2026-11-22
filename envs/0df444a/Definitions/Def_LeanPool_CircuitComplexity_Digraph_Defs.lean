-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
-- name    : LeanPool_CircuitComplexity_Digraph_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:34.584245+00:00
-- url     : https://prove2.me/theorems/c215f5d3-4b42-48c7-9fd9-efd601ff69bc
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Digraph/Defs.lean

module
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Lattice.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Digraph
variable {V : Type*}
def IsDirectedPath (G : Digraph V) {m : Nat} (p : Fin m → V) : Prop :=
  ∀ i : Fin m, ∀ h : i.val + 1 < m, G.Adj (p i) (p ⟨i.val + 1, h⟩)
def IsSimplePath (G : Digraph V) {m : Nat} (p : Fin m → V) : Prop :=
  G.IsDirectedPath p ∧ Function.Injective p
noncomputable def depth (G : Digraph V) : Nat :=
  sSup { m | ∃ p : Fin m → V, G.IsDirectedPath p }
def edgeFinset [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] : Finset (V × V) :=
  have _hV : DecidableEq V := ‹_›
  Finset.univ.filter (fun p => G.Adj p.1 p.2)
def deleteEdges (G : Digraph V) (F : Finset (V × V)) : Digraph V where
  Adj u v := G.Adj u v ∧ (u, v) ∉ F
instance [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (F : Finset (V × V)) : DecidableRel (G.deleteEdges F).Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj u v ∧ _))
def IsAcyclic (G : Digraph V) : Prop :=
  BddAbove { m | ∃ p : Fin m → V, G.IsDirectedPath p }
end Digraph


