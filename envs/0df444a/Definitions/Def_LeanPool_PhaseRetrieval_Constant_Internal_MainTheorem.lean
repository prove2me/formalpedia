-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_MainTheorem
-- name    : LeanPool_PhaseRetrieval_Constant_Internal_MainTheorem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:01:36.131432+00:00
-- url     : https://prove2.me/theorems/be54206c-08d7-4645-8234-578f5c7c20a4
-- title:
--   Main Theorem
-- statement:
--   Definitions and structural lemmas for Main Theorem, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/MainTheorem.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_AnnulusLocalEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LeakageEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Complex Real Finset Polynomial
noncomputable section
namespace FockSPR
end FockSPR


