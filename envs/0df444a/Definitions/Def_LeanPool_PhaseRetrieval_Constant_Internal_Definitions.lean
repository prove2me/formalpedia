-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
-- name    : LeanPool_PhaseRetrieval_Constant_Internal_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:59:06.028109+00:00
-- url     : https://prove2.me/theorems/a4f0a25c-3981-4288-914f-c9b7bc7e31f1
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/Definitions.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Gamma
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Complex Real Finset
open scoped ENNReal NNReal
noncomputable section
namespace FockSPR
def T : ℝ := 2 * Real.pi
lemma T_pos : 0 < T := mul_pos two_pos Real.pi_pos
instance : Fact (0 < T) := ⟨T_pos⟩
def rho (w : ℂ) : ℝ := |‖(1 : ℂ) + w‖ - 1|
def polyEval {D : ℕ} (a : Fin D → ℂ) (z : ℂ) : ℂ :=
  ∑ k : Fin D, a k * z ^ (k.val + 1)
def polyEvalCircle {D : ℕ} (a : Fin D → ℂ) (r : ℝ) : AddCircle T → ℂ :=
  fun t => ∑ k : Fin D, a k * (r : ℂ) ^ (k.val + 1) * fourier ((k.val + 1 : ℕ) : ℤ) t
def fockNormSq {D : ℕ} (a : Fin D → ℂ) : ℝ :=
  ∑ k : Fin D, ‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ)
def rhoFockNormSq {D : ℕ} (a : Fin D → ℂ) : ℝ :=
  (1 / Real.pi) * ∫ z : ℂ, (rho (polyEval a z)) ^ 2 * Real.exp (-‖z‖ ^ 2)
def circleNormSq (f : AddCircle T → ℂ) : ℝ :=
  ∫ t, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle
end FockSPR


