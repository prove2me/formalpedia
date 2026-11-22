-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
-- name    : LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:13:31.696956+00:00
-- url     : https://prove2.me/theorems/fe5ffa5e-a15b-4bc5-a299-0c28bb595195
-- title:
--   Nakano
-- statement:
--   Definitions and structural lemmas for Nakano, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Nakano.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BanachLattice
section Forward
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]
end Forward
section Sigma
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
@[reducible]
noncomputable def sigmaConditionallyCompleteLatticeOfMonoBddAboveTendsto
    (h : ∀ {u : ℕ → X}, Monotone u → BddAbove (Set.range u) →
      ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x)) :
    SigmaConditionallyCompleteLattice X := by
  haveI : Nonempty X := ⟨0⟩
  refine sigmaConditionallyCompleteLatticeOfPosSeq X
    (fun {u} hmono _ hbd => ?_)
  obtain ⟨x, hx, _⟩ := h hmono hbd
  exact ⟨x, hx⟩
variable [BanachLattice X]
end Sigma
section Backward
variable {X : Type*} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X] [IsSigmaOrderContinuousNorm X]
end Backward
end BanachLattice


