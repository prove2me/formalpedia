-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
-- name    : LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:42:42.648821+00:00
-- url     : https://prove2.me/theorems/024e5dbb-8f99-452a-bc07-6740834cb6f7
-- title:
--   Deletion Coordinates
-- statement:
--   Definitions and structural lemmas for Deletion Coordinates, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
section Cuts
def IsJunction (δ : ℕ) (cs : Finset ℕ) (a : ℕ) : Prop :=
  ∃ c ∈ cs, retainedCount (sitePositions δ cs) c = a
instance (δ : ℕ) (cs : Finset ℕ) (a : ℕ) : Decidable (IsJunction δ cs a) :=
  inferInstanceAs (Decidable (∃ c ∈ cs, _))
variable {δ : ℕ} {cs : Finset ℕ}
end Cuts
section Matched
variable {α : Type} {δ : ℕ}
end Matched
section Generic
variable {α : Type} [DecidableEq α] {k : ℕ}
end Generic
end DeciSigma1.Holes.Fresh


