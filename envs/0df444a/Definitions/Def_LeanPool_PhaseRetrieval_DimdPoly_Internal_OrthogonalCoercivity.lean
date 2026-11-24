-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:17:51.615301+00:00
-- url     : https://prove2.me/theorems/9ee03eab-e70b-4cba-8cf6-3e764d09eef9
-- title:
--   Orthogonal Coercivity
-- statement:
--   Definitions and structural lemmas for Orthogonal Coercivity, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/OrthogonalCoercivity.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseAnnulusEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Complex
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
section
variable {d : Nat} (kappa : MultiIndex d)
local notation "Pk" => Pkappa d kappa
def coeffPk (H : Pk) (alpha : Idx d) : ℂ := coeffPkappa H alpha
def OrthogonalToPk (F G : Pk) : Prop := orthogonalToPk F G
def defectPk (F G : Pk) : ℝ := defect F G
def lowAnnulusMassPk (J : Nat) (H : Pk) : ℝ := lowAnnulusMass J (ofPkappa kappa H)
def highAnnulusMassPk (J : Nat) (H : Pk) : ℝ := highAnnulusMass J (ofPkappa kappa H)
end
end DimdPolyLEAN


