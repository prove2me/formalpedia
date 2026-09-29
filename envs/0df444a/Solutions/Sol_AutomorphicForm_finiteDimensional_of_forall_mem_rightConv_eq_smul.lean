-- Prove2me | solution 1 for AutomorphicForm.finiteDimensional_of_forall_mem_rightConv_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/17bbac35-4ef9-571b-8f82-8f872fe52c26

import Definitions.Def_AutomorphicForm_CuspidalConstituent

import Theorems.Thm_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_smul
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_smul.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

namespace AutomorphicForm
p2m_export "AutomorphicForm" "productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup IsSmoothCuspAutomorphicFnAt rightConv archEntries IsFactorizableTestFn finiteDimensional_of_forall_mem_rightConv_eq_self"
namespace C8EigenSlice
p2m_open "AutomorphicForm"

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem isFactorizableTestFn_const_smul {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (a : ℂ) :
    IsFactorizableTestFn F (fun x => a * f x) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩, hff, hfac⟩ := hf
  refine ⟨fun y => a * fa y, ff, ⟨⟨fun e => a * Φ e, contDiff_const.mul hΦ, fun g => by
      show a * fa g = a * Φ (archEntries F g); rw [hfaΦ]⟩, ?_⟩, hff,
    fun g => by show a * f g = a * fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g); rw [hfac, mul_assoc]⟩
  exact hsupp.mul_left

theorem rightConv_const_mul_right (φ f : AdelicGL2 (𝓞 F) F → ℂ) (a : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ (fun x => a * f x) g = a * rightConv F φ f g := by
  simp only [rightConv]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

end AutomorphicForm.C8EigenSlice

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (lam : ℂ) (hlam : lam ≠ 0)
    (E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hE : ∀ φ ∈ E, IsSmoothCuspAutomorphicFnAt F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ φ ∧
      Continuous φ ∧ rightConv F φ f = lam • φ) :
    FiniteDimensional ℂ ↥E := by
  refine AutomorphicForm.finiteDimensional_of_forall_mem_rightConv_eq_self F c u d₁ d₂ T hc hd₁ hd hcov ξ
    (fun x => lam⁻¹ * f x) (AutomorphicForm.C8EigenSlice.isFactorizableTestFn_const_smul hf lam⁻¹) E
    fun φ hφ => ?_
  obtain ⟨h1, h2, h3⟩ := hE φ hφ
  refine ⟨h1, h2, ?_⟩
  funext g
  rw [AutomorphicForm.C8EigenSlice.rightConv_const_mul_right, h3, Pi.smul_apply, smul_eq_mul,
    inv_mul_cancel_left₀ hlam]

end S_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_smul (solution)
