-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
-- name    : LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:00:00.903845+00:00
-- url     : https://prove2.me/theorems/34fc113f-4dac-440e-a20f-2ac4d7fc9e15
-- title:
--   High Freq Band Estimate
-- statement:
--   Definitions and structural lemmas for High Freq Band Estimate, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/HighFreqBandEstimate.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_MissingMathlib_Poincare
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_RotationalAveraging
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_SafeSquare
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Complex Real Finset
noncomputable section
namespace FockSPR
def slowFactor {L : ℕ} (b : Fin L → ℂ) :
    AddCircle T → ℂ :=
  fun t => ∑ m : Fin L, b m * fourier (m.val : ℤ) t
def iLeft (N : ℕ) (k : ℕ) : ℝ :=
  T * k / N
def qAvg {L : ℕ} (b : Fin L → ℂ)
    (N : ℕ) (k : Fin N) : ℂ :=
  (↑N / (T : ℂ)) •
    ∫ t in iLeft N k.val..iLeft N (k.val + 1),
      slowFactor b (↑t : AddCircle T)
def totalDelta {L : ℕ} (b : Fin L → ℂ)
    (N : ℕ) : ℝ :=
  (1 / T) * ∑ k : Fin N,
    ∫ t in iLeft N k.val..iLeft N (k.val + 1),
      ‖slowFactor b (↑t : AddCircle T) -
        qAvg b N k‖ ^ 2
end FockSPR


