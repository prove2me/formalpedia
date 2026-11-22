-- Prove2me | Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
-- name    : LeanPool_OrderClosures_GaoLeungProblem_Counterexample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:56:24.209037+00:00
-- url     : https://prove2.me/theorems/cc8b742c-b042-49eb-9984-4f9bb8ca9a67
-- title:
--   Counterexample
-- statement:
--   Definitions and structural lemmas for Counterexample, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean

module
public import Mathlib.Data.Fintype.Order
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungCharacterization
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Ordinal.CantorNormalForm
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace OrderClosures
open Set
universe u v
section GaoLeungTheorem
def GaoLeungProperty (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Prop :=
  ∀ Y : VectorSublattice X, IsOrderClosed (uoAdherence (Y : Set X))
end GaoLeungTheorem
section Counterexample
def positiveSubsetSuprema
    {X : Type u} [AddCommGroup X] [Lattice X]
    (S : Set X) : Set X :=
  {x | ∃ A : Set X, A ⊆ S ∩ Ici 0 ∧ IsLUB A x}
def signedPositiveSubsetSuprema
    {X : Type u} [AddCommGroup X] [Lattice X]
    (S : Set X) : Set X :=
  {x | x⁺ ∈ positiveSubsetSuprema S ∧ x⁻ ∈ positiveSubsetSuprema S}
end Counterexample
end OrderClosures


