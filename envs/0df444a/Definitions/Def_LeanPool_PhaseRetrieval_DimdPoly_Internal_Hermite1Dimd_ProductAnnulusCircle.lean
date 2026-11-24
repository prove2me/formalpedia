-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductAnnulusCircle
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductAnnulusCircle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:04:11.955818+00:00
-- url     : https://prove2.me/theorems/0f543b61-1d46-47a7-ac33-df4558febb5f
-- title:
--   Product Annulus Circle
-- statement:
--   Definitions and structural lemmas for Product Annulus Circle, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductAnnulusCircle.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_DegreeBookkeeping
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
def orbitCoeff
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) (n : ℕ) : ℂ :=
  ∑ α ∈ (localPart j M G).support.filter (fun α => totalDegree α = n),
    (localPart j M G).coeff α * PhiKappaAlpha κ α z
def localOrbit
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) (t : Circle) : ℂ :=
  (fourier (totalDegree κ : ℤ) t : ℂ) *
    evalHermiteSum κ (localPart j M G)
      (fun q => (fourier (1 : ℤ) t : ℂ) * z q)
end Hermite1DimdLEAN


