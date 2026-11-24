-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalHelpers
-- name    : LeanPool_PhaseRetrieval_Constant_Internal_LocalHelpers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:02:52.426273+00:00
-- url     : https://prove2.me/theorems/138f97bf-4d18-4036-a939-84aa80930d38
-- title:
--   Local Helpers
-- statement:
--   Definitions and structural lemmas for Local Helpers, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LocalHelpers.lean

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCore
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open FockSPR MeasureTheory Complex Real Polynomial Finset
open scoped ENNReal ComplexConjugate
noncomputable section
namespace FockSPR
def phaseDistanceSq (p : Polynomial ℂ) (lam : ℂ) : ℝ :=
  ∫ z : ℂ, ‖(1 : ℂ) + p.eval z - lam‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
def phaseDistanceSqNorm (p : Polynomial ℂ) (lam : ℂ) : ℝ :=
  (1 / Real.pi) * phaseDistanceSq p lam
def phaseAnchor (w : ℂ) : ℂ :=
  if _hw : w = 0 then 1 else w / ‖w‖
end FockSPR


