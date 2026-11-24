-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LeakageEstimate
-- name    : LeanPool_PhaseRetrieval_Constant_Internal_LeakageEstimate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:00:00.700803+00:00
-- url     : https://prove2.me/theorems/42fb51b0-1c91-4ec9-aaa9-1fedd843714a
-- title:
--   Leakage Estimate
-- statement:
--   Definitions and structural lemmas for Leakage Estimate, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LeakageEstimate.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Real Finset Complex
noncomputable section
namespace FockSPR
def etaCoeff (M : ℕ) (bound : ℕ) : ℝ :=
  2 * Real.exp (1 / 4) * ∑ m ∈ Finset.Icc M bound, Real.exp (-(m : ℝ) ^ 2)
def fockNormSqBlock {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) : ℝ :=
  ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
    then ‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ) else 0
end FockSPR


