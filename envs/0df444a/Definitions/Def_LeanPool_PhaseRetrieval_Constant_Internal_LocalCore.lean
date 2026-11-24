-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCore
-- name    : LeanPool_PhaseRetrieval_Constant_Internal_LocalCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:02:18.934925+00:00
-- url     : https://prove2.me/theorems/a5d848bc-9bea-445b-8706-6cf695fdb89a
-- title:
--   Local Core
-- statement:
--   Definitions and structural lemmas for Local Core, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LocalCore.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_MainTheorem
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open FockSPR MeasureTheory Complex Real Polynomial Finset
open scoped ENNReal ComplexConjugate
noncomputable section
namespace FockSPR
def gaussianWeight (z : ℂ) : ℝ :=
  (1 / Real.pi) * Real.exp (-‖z‖ ^ 2)
def gaussianMeasure : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (gaussianWeight z))
end FockSPR


