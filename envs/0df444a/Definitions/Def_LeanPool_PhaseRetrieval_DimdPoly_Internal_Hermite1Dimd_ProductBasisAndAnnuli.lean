-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:02:44.426512+00:00
-- url     : https://prove2.me/theorems/2325f961-87ea-4aac-a047-7a13bafae9f2
-- title:
--   Product Basis And Annuli
-- statement:
--   Definitions and structural lemmas for Product Basis And Annuli, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.NormNum.Parity
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


set_option autoImplicit true
@[expose] public section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
def mulCircleLIE (ω : _root_.Circle) : ℂ ≃ₗᵢ[ℝ] ℂ := by
  refine LinearIsometryEquiv.mk
    (LinearEquiv.ofBijective
      (LinearMap.mulLeft ℝ ((ω : ℂ)))
      ?_)
    ?_
  · refine ⟨?inj, ?surj⟩
    · intro x y hxy
      exact mul_left_cancel₀ (Circle.coe_ne_zero ω) (by simpa using hxy)
    · intro z
      refine ⟨((ω⁻¹ : _root_.Circle) : ℂ) * z, ?_⟩
      simp []
  · intro x
    change ‖(ω : ℂ) * x‖ = ‖x‖
    have hω : ‖(ω : ℂ)‖ = 1 := Circle.norm_coe ω
    rw [norm_mul, hω, one_mul]
end Hermite1DimdLEAN


