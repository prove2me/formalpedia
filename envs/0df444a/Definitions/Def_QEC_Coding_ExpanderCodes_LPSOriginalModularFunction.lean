-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:00:51.940574+00:00
-- url     : https://prove2.me/theorems/8e42fac5-9235-4122-9b42-cfffbbaa9098
-- title:
--   LPSOriginal Modular Function
-- statement:
--   Definitions and structural lemmas for LPSOriginal Modular Function, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalJInvariant (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ^3/ModularForm.discriminant τ
lemma lpsOriginalJInvariant_SL_invariant (g : GL (Fin 2) ℝ)
    (hg : g∈(𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) (τ : ℍ) :
    lpsOriginalJInvariant (g • τ)=lpsOriginalJInvariant τ := by
  have h4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hg τ
  have h12 := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hg τ
  simp only [zpow_ofNat] at h4 h12
  change ModularForm.E₄ (g • τ)^3/ModularForm.discriminant (g • τ)=
    ModularForm.E₄ τ^3/ModularForm.discriminant τ
  rw [h4,show ModularForm.discriminant (g • τ)=
    UpperHalfPlane.denom g τ^12*ModularForm.discriminant τ from h12]
  field_simp [UpperHalfPlane.denom_ne_zero g τ]
def lpsOriginalJQCoefficient (q : ℂ) : ℂ :=
  (UpperHalfPlane.cuspFunction 1 ModularForm.E₄ q)^3 /
    dslope (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) 0 q
lemma lpsOriginalJInvariant_Gamma0_invariant (N : ℕ) (g : GL (Fin 2) ℝ)
    (hg : g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (τ : ℍ) :
    lpsOriginalJInvariant (g•τ)=lpsOriginalJInvariant τ := by
  apply lpsOriginalJInvariant_SL_invariant g _ τ
  obtain ⟨γ,_,hγ⟩ := hg
  exact ⟨γ,hγ⟩
def lpsOriginalJQuotient (N : ℕ) : MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → ℂ :=
  Quotient.lift lpsOriginalJInvariant (by
    intro τ σ h
    change MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ τ σ at h
    rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at h
    obtain ⟨g,hg⟩ := h
    rw [←hg]
    exact lpsOriginalJInvariant_Gamma0_invariant N g.val g.property σ)
lemma lpsOriginalCuspGroup_width_integer (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    ∃ m : ℕ, 0<m ∧ (lpsOriginalCuspGroup N ρ).strictWidthInfty=(m:ℝ) := by
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have hg := lpsOriginalCuspGroup_le_SLRange N ρ (Subgroup.mem_strictPeriods_iff.mp hp)
  obtain ⟨γ,hγ⟩ := hg
  have he := congrArg (fun g : GL (Fin 2) ℝ => g 0 1) hγ
  let z : ℤ := γ 0 1
  have hz : (z:ℝ)=(lpsOriginalCuspGroup N ρ).strictWidthInfty := by
    simpa [z,Matrix.SpecialLinearGroup.mapGL_coe_matrix,Matrix.GeneralLinearGroup.upperRightHom] using he
  have hzR : (0:ℝ)<(z:ℝ) := by rw [hz];exact lpsOriginalCuspGroup_width_positive N ρ
  have hzpos : 0<z := by exact_mod_cast hzR
  refine ⟨z.toNat,by omega,?_⟩
  rw [←hz]
  exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hzpos)).symm
def lpsOriginalCuspWidthNat (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) : ℕ :=
  (lpsOriginalCuspGroup_width_integer N ρ).choose
def lpsOriginalFilledJ (N : ℕ) : LPSOriginalFilledCurve N → ℂ :=
  Sum.elim (lpsOriginalJQuotient N) (fun _ => 0)
end
end QEC.Coding.TannerLiftedProduct


