-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
-- name    : LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:59:35.42292+00:00
-- url     : https://prove2.me/theorems/51b71f12-d6ac-4d5b-b884-301ce6f1ba07
-- title:
--   Block Decomposition
-- statement:
--   Definitions and structural lemmas for Block Decomposition, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Nat Real MeasureTheory
noncomputable section
namespace FockSPR
def freqBlock (ℓ : ℕ) : Finset ℕ :=
  Finset.Icc (ℓ ^ 2) ((ℓ + 1) ^ 2 - 1)
def blockPoly {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) (z : ℂ) : ℂ :=
  ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ then a k * z ^ (k.val + 1) else 0
def maxBlockIndex (D : ℕ) : ℕ := Nat.sqrt D
def localPoly {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) (z : ℂ) : ℂ :=
  ∑ ℓ ∈ Finset.Icc (max 1 (j - M)) (min (maxBlockIndex D) (j + M)),
    blockPoly a ℓ z
def remainderPoly {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) (z : ℂ) : ℂ :=
  polyEval a z - localPoly a M j z
end FockSPR


