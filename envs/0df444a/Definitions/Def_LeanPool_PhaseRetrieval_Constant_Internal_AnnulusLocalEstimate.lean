-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_AnnulusLocalEstimate
-- name    : LeanPool_PhaseRetrieval_Constant_Internal_AnnulusLocalEstimate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:00:49.647508+00:00
-- url     : https://prove2.me/theorems/96b107ec-65db-4af8-9328-bcb386ec013d
-- title:
--   Annulus Local Estimate
-- statement:
--   Definitions and structural lemmas for Annulus Local Estimate, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/AnnulusLocalEstimate.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCircleEstimate
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Complex Real Finset
noncomputable section
namespace FockSPR
def activeFreqSet (D j : ℕ) : Finset ℕ :=
  ((Finset.Icc (max 1 (j - 5))
    (min (maxBlockIndex D) (j + 5))).biUnion freqBlock).filter (· ≤ D)
def localFourierCoeff {D : ℕ} (a : Fin D → ℂ) (j : ℕ) (r : ℝ) : ℕ → ℂ :=
  fun n =>
    if h : n ∈ (Finset.Icc (max 1 (j - 5))
        (min (maxBlockIndex D) (j + 5))).biUnion freqBlock ∧
        1 ≤ n ∧ n ≤ D then
      a ⟨n - 1, by omega⟩ * (↑r : ℂ) ^ n
    else 0
end FockSPR


