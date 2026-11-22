-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
-- name    : LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:43:33.446802+00:00
-- url     : https://prove2.me/theorems/f1df6e9d-5219-4482-b6cb-31410372efd6
-- title:
--   Channel Preservation
-- statement:
--   Definitions and structural lemmas for Channel Preservation, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
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
end BlockDeletion
end Sites
end DeciSigma1.Holes.Fresh


