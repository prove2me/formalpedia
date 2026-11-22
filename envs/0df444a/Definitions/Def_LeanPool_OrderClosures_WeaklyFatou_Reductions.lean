-- Prove2me | Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
-- name    : LeanPool_OrderClosures_WeaklyFatou_Reductions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:55:24.920802+00:00
-- url     : https://prove2.me/theorems/e1d3590c-0c29-4a1e-8f5a-8d065c743265
-- title:
--   Reductions
-- statement:
--   Definitions and structural lemmas for Reductions, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
section Reductions
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
def IsWeakSequentialNakanoConstant (p : X → ℝ) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ (x : ℕ → X), Monotone x → (∀ m, 0 ≤ x m) →
    BddAbove (Set.range x) → (∀ m, p (x m) ≤ 1) →
      ∀ ε > 0, ∃ y : X, 0 ≤ y ∧ (∀ m, x m ≤ y) ∧ p y ≤ K + ε
def IsWeakNakanoConstant (p : X → ℝ) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ A : Set X, A ⊆ Ici 0 → DirectedOn (· ≤ ·) A → BddAbove A →
    (∀ x ∈ A, p x ≤ 1) → ∀ ε > 0,
      ∃ y : X, 0 ≤ y ∧ (∀ x ∈ A, x ≤ y) ∧ p y ≤ K + ε
def FremlinProperty : Prop :=
  ∀ p : PaperLatticeNorm X, IsCompleteFor p →
    (∃ K, HasWeakFatouProperty p K) →
      ∃ q : PaperLatticeNorm X, HasFatouProperty q ∧ EquivalentNorms p q
end Reductions
end OrderClosures


