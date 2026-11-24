-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:01:19.367517+00:00
-- url     : https://prove2.me/theorems/ee0cf939-e132-4eaf-8443-fd9418f89f62
-- title:
--   Orthogonal Reduction
-- statement:
--   Definitions and structural lemmas for Orthogonal Reduction, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/OrthogonalReduction/OrthogonalReduction.lean

module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
open Complex MeasureTheory Real
namespace OrthogonalReduction
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω)
variable [MeasureTheory.SigmaFinite μ]
def localDefect (ι : H →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 μ) (f0 : H) (h : H) : ℝ :=
  MeasureTheory.lpNorm
    (fun x : Ω => ‖(ι (h + f0) : Ω → ℂ) x‖ - ‖(ι f0 : Ω → ℂ) x‖)
    2 μ
end OrthogonalReduction


