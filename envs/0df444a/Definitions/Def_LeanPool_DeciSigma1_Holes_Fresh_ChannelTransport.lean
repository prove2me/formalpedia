-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
-- name    : LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:43:05.568003+00:00
-- url     : https://prove2.me/theorems/77d6612d-4d6a-4ebe-a59c-0a4d7ea0c6ea
-- title:
--   Channel Transport
-- statement:
--   Definitions and structural lemmas for Channel Transport, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
section Sites
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
namespace BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
def upperCutLength : ℕ := firstBlocksLength m.edge.blocks.reverse m.minDepth
def deletedText :
    List α := (((m.edge.blocks.reverse.take m.maxDepth).drop m.minDepth).reverse).flatten
end BlockDeletion
end Sites
end DeciSigma1.Holes.Fresh


