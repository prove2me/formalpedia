-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:02:09.01242+00:00
-- url     : https://prove2.me/theorems/85efa4b5-590e-40e6-afe2-dfd4f81ba822
-- title:
--   Imported Analytic Inputs
-- statement:
--   Definitions and structural lemmas for Imported Analytic Inputs, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ImportedAnalyticInputs.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
def oneDimLift (f : ℂ → ℂ) : CSpace 1 → ℂ := fun z => f (z 0)
def bandCoeff (N L : ℕ) (c : Fin L → ℂ) : ℕ → ℂ :=
  fun n => if h : N ≤ n ∧ n < N + L then c ⟨n - N, by omega⟩ else 0
end Hermite1DimdLEAN


