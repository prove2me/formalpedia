-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T01:29:47.792432+00:00
-- url     : https://prove2.me/theorems/5df4d8c9-7666-48bf-bbe3-ac187ea69d85
-- title:
--   LPSOriginal Meromorphic Modular Ratio
-- statement:
--   Definitions and structural lemmas for LPSOriginal Meromorphic Modular Ratio, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalMeromorphicDeltaQCoefficient (q : ℂ) : ℂ :=
  dslope (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) 0 q
def lpsOriginalFilledFunctionSlashInvariant
    (N : ℕ) (F : LPSOriginalFilledCurve N → ℂ) :
    SlashInvariantForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 0 where
  toFun τ := F (Sum.inl ⟦τ⟧)
  slash_action_eq' g hg := by
    funext τ
    have he : (⟦g • τ⟧ : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) = ⟦τ⟧ := by
      apply Quotient.sound
      change MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ (g • τ) τ
      rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
      exact ⟨⟨g,hg⟩,rfl⟩
    simp [ModularForm.slash_def,UpperHalfPlane.σ,
      Subgroup.HasDetOne.det_eq hg,he]
lemma lpsOriginalFilledFunction_delta_slash
    (N : ℕ) (F : LPSOriginalFilledCurve N → ℂ) (k : ℕ) (ρ : SL(2,ℤ)) :
    (fun τ : ℍ => ModularForm.discriminant τ ^ k * F (Sum.inl ⟦τ⟧))
      ∣[((k : ℤ)*12)] ρ =
      (fun τ : ℍ => ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  let D := (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k
  have hD : (D : ℍ → ℂ) ∣[(k : ℤ)*12] ρ = D :=
    SlashInvariantForm.slash_action_eqn D _ ⟨ρ,rfl⟩
  have hh := ModularForm.mul_slash_SL2 ((k : ℤ)*12) 0 ρ
    (D : ℍ → ℂ) (fun τ : ℍ => F (Sum.inl ⟦τ⟧))
  rw [add_zero,hD] at hh
  have hfun : (D : ℍ → ℂ) = (fun τ : ℍ => ModularForm.discriminant τ ^ k) := by
    rw [show D = (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k from rfl,
      ModularForm.coe_pow]
    rfl
  rw [hfun] at hh
  refine hh.trans ?_
  funext τ
  simp only [Pi.mul_apply,ModularForm.SL_slash_apply,neg_zero,zpow_zero,mul_one]
  rfl
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Construct the actual Delta-cleared modular form from proved holomorphy and cusp boundedness. -/
def lpsOriginalFilledFunctionDeltaModularForm
    (N : ℕ) [NeZero N] (F : LPSOriginalFilledCurve N → ℂ) (k : ℕ)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => F (Sum.inl ⟦τ⟧)))
    (hb : ∀ ρ : SL(2,ℤ), UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : ℍ => ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧))) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ((k : ℤ)*12) where
  toFun τ := ModularForm.discriminant τ ^ k * F (Sum.inl ⟦τ⟧)
  slash_action_eq' g hg := by
    let D := (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k
    have hle : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
      intro g hg
      obtain ⟨γ,hγ,he⟩ := hg
      exact ⟨γ,he⟩
    have hD := SlashInvariantForm.slash_action_eqn D g (hle hg)
    have hZ := SlashInvariantForm.slash_action_eqn
      (lpsOriginalFilledFunctionSlashInvariant N F) g hg
    have hh := ModularForm.mul_slash ((k : ℤ)*12) 0 g
      (D : ℍ → ℂ) (lpsOriginalFilledFunctionSlashInvariant N F : ℍ → ℂ)
    rw [add_zero,hD,hZ] at hh
    have hd : |(g.det : ℝ)| = 1 := by
      simp [Subgroup.HasDetOne.det_eq hg]
    rw [hd,one_smul] at hh
    have hfun : (D : ℍ → ℂ) = (fun τ : ℍ => ModularForm.discriminant τ ^ k) := by
      rw [show D = (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k from rfl,
        ModularForm.coe_pow]
      rfl
    rw [hfun] at hh
    exact hh
  holo' := (ModularFormClass.holo CuspForm.discriminant).pow k |>.mul hF
  bdd_at_cusps' {c} hc := by
    have hcSL := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))).mp hc
    apply (OnePoint.isBoundedAt_iff_forall_SL2Z hcSL).mpr
    intro ρ hρ
    rw [lpsOriginalFilledFunction_delta_slash]
    exact hb ρ
def lpsOriginalMeromorphicDeltaPowerAtLevel
    (N : ℕ) (k : ℕ) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ((k : ℤ)*12) :=
  let D := (CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow k
  let hle : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
    intro g hg
    obtain ⟨γ,hγ,he⟩ := hg
    exact ⟨γ,he⟩
  { toFun := D
    slash_action_eq' g hg := D.slash_action_eq' g (hle hg)
    holo' := D.holo'
    bdd_at_cusps' hc := D.bdd_at_cusps' (hc.mono hle) }
end
end QEC.Coding.TannerLiftedProduct


