-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
-- name    : LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:58:44.916263+00:00
-- url     : https://prove2.me/theorems/03f8a272-1863-43d4-ae0d-8c4883b51d61
-- title:
--   Laplace Factorial
-- statement:
--   Definitions and structural lemmas for Laplace Factorial, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LaplaceFactorial.lean

module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Real MeasureTheory Set
noncomputable section
namespace FockSPR
def rStar (n : ℕ) : ℝ := Real.sqrt (n + 1 / 2)
def phiFunc (n : ℕ) (r : ℝ) : ℝ := (2 * n + 1) * Real.log r - r ^ 2
def hFunc (n : ℕ) (r : ℝ) : ℝ := phiFunc n r + (r - rStar n) ^ 2
def distToInterval (x : ℝ) (j : ℕ) : ℝ :=
  max (max ((j : ℝ) - x) (x - (j + 1 : ℝ))) 0
end FockSPR


