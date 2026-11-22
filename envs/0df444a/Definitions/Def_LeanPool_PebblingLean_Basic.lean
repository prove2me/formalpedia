-- Prove2me | Definitions.Def_LeanPool_PebblingLean_Basic
-- name    : LeanPool_PebblingLean_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:45:52.572014+00:00
-- url     : https://prove2.me/theorems/5f8af4c5-f87d-4aeb-9c60-94439d787f99
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
universe u
structure Graph (V : Type u) where
  /-- The adjacency relation between vertices. -/
  Adj : V → V → Prop
  /-- Adjacency is symmetric. -/
  symm : ∀ {u v : V}, Adj u v → Adj v u
  /-- The graph has no self-loops. -/
  loopless : ∀ v : V, ¬ Adj v v
namespace Graph
variable {V : Type u} (G : Graph V)
end Graph
abbrev Pebbling (V : Type u) := V → ℕ
namespace Pebbling
variable {V : Type u}
def size [Fintype V] (D : Pebbling V) : ℕ :=
  ∑ v, D v
def Dominates (D E : Pebbling V) : Prop :=
  ∀ v : V, E v ≤ D v
def moveDistribution [DecidableEq V] (D : Pebbling V) (u v : V) : Pebbling V :=
  fun x =>
    if x = u then D x - 2
    else if x = v then D x + 1
    else D x
def Move [DecidableEq V] (G : Graph V) (D E : Pebbling V) : Prop :=
  ∃ u v : V,
    G.Adj u v ∧
      2 ≤ D u ∧
        E = moveDistribution D u v
def Reaches [DecidableEq V] (G : Graph V) (D E : Pebbling V) : Prop :=
  Relation.ReflTransGen (Move G) D E
def CanReachAtLeast [DecidableEq V] (G : Graph V) (D : Pebbling V) (target : V) (T : ℕ) :
    Prop :=
  ∃ E : Pebbling V, Reaches G D E ∧ T ≤ E target
def CanReach [DecidableEq V] (G : Graph V) (D : Pebbling V) (target : V) : Prop :=
  CanReachAtLeast G D target 1
def SolvableAtLeast [DecidableEq V] (G : Graph V) (D : Pebbling V) (T : ℕ) : Prop :=
  ∀ target : V, CanReachAtLeast G D target T
def Solvable [DecidableEq V] (G : Graph V) (D : Pebbling V) : Prop :=
  SolvableAtLeast G D 1
def HasSolvableSize [Fintype V] [DecidableEq V] (G : Graph V) (k : ℕ) : Prop :=
  ∃ D : Pebbling V, size D = k ∧ Solvable G D
def HasSolvableAtLeastSize [Fintype V] [DecidableEq V] (G : Graph V) (T k : ℕ) : Prop :=
  ∃ D : Pebbling V, size D = k ∧ SolvableAtLeast G D T
def HasSolvableAtMostSize [Fintype V] [DecidableEq V] (G : Graph V) (T k : ℕ) : Prop :=
  ∃ D : Pebbling V, size D ≤ k ∧ SolvableAtLeast G D T
def MinOccupiedPileSize (D : Pebbling V) (S : ℕ) : Prop :=
  ∀ v : V, D v ≠ 0 → S ≤ D v
def supportSize [Fintype V] (D : Pebbling V) : ℕ :=
  (Finset.univ.filter fun v => D v ≠ 0).card
def IsOptimalNumber [Fintype V] [DecidableEq V] (G : Graph V) (k : ℕ) : Prop :=
  HasSolvableSize G k ∧ ∀ l : ℕ, l < k → ¬ HasSolvableSize G l
def IsOptimalDemandNumber [Fintype V] [DecidableEq V] (G : Graph V) (T k : ℕ) : Prop :=
  HasSolvableAtLeastSize G T k ∧ ∀ l : ℕ, l < k → ¬ HasSolvableAtLeastSize G T l
end Pebbling
end PebblingLean


