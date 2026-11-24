-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:59:39.20427+00:00
-- url     : https://prove2.me/theorems/00e180d1-b540-4594-9170-07c15788acec
-- title:
--   Basis Localization
-- statement:
--   Definitions and structural lemmas for Basis Localization, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/BasisLocalization.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Complex MeasureTheory Real Finset
noncomputable section
namespace HermitekLEAN
noncomputable def Pkn (k n : ℕ) : Polynomial ℝ :=
  Finset.sum (Finset.range (k + 1)) (fun j =>
    Polynomial.C (((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) * (Nat.descFactorial n j : ℝ)) *
      Polynomial.X ^ (k - j))
def singleCoeff (n : ℕ) : Fin (n + 1) → ℂ :=
  fun m => if m.1 = n then 1 else 0
def phi0AnnulusIntegrand (k : ℕ) (g0normsq : ℝ) (r : ℝ) : ℝ :=
  r * (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * g0normsq) * Real.exp (-r ^ 2)
end HermitekLEAN


