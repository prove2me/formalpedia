-- Prove2me | Definitions.Def_LeanPool_PebblingLean_Product
-- name    : LeanPool_PebblingLean_Product
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:46:16.421295+00:00
-- url     : https://prove2.me/theorems/b890f8d7-db0e-4623-aad7-883aa6b91753
-- title:
--   Product
-- statement:
--   Definitions and structural lemmas for Product, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
universe u v
namespace Graph
variable {V : Type u} {W : Type v}
def cartesianProduct (G : Graph V) (H : Graph W) : Graph (V × W) where
  Adj p q :=
    (G.Adj p.1 q.1 ∧ p.2 = q.2) ∨ (p.1 = q.1 ∧ H.Adj p.2 q.2)
  symm := by
    intro p q h
    rcases h with h | h
    · exact Or.inl ⟨G.symm h.1, h.2.symm⟩
    · exact Or.inr ⟨h.1.symm, H.symm h.2⟩
  loopless := by
    intro p h
    rcases h with h | h
    · exact (G.loopless p.1) h.1
    · exact (H.loopless p.2) h.2
end Graph
namespace Pebbling
variable {V : Type u} {W : Type v}
def fibersDistribution (F : W → Pebbling V) : Pebbling (V × W) :=
  fun p => F p.2 p.1
def replaceFiber [DecidableEq W] (F : W → Pebbling V) (z : W) (E : Pebbling V) :
    W → Pebbling V :=
  fun z' => if z' = z then E else F z'
def updateFibers [DecidableEq W] (F F' : W → Pebbling V) (s : Finset W) :
    W → Pebbling V :=
  fun z => if z ∈ s then F' z else F z
def sliceDistribution [DecidableEq V] (x : V) (E : Pebbling W) : Pebbling (V × W) :=
  fun p => if p.1 = x then E p.2 else 0
end Pebbling
end PebblingLean


