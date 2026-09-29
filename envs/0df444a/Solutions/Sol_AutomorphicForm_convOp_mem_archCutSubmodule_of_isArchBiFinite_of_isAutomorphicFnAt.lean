-- Prove2me | solution 1 for AutomorphicForm.convOp_mem_archCutSubmodule_of_isArchBiFinite_of_isAutomorphicFnAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1e9aa6ac-54c3-5e15-9639-c07983da106d

import Theorems.Thm_AutomorphicForm_memLp_two_restrict_of_isCompact_of_isAutomorphicFnAt_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_convOp_mem_archCutSubmodule_of_isArchBiFinite_of_isAutomorphicFnAt
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm

namespace Ws31
namespace T6d

theorem rowIsometryInclAt₀_injective (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    Function.Injective (rowIsometryInclAt₀ F w) := by
  intro k₁ k₂ h
  have h1 := congrArg (fun g => archComponent F w (glArch (𝓞 F) F g)) h
  simp only [rowIsometryInclAt₀_apply] at h1
  change archComponent F w (glArch (𝓞 F) F ((adelicArchGLIncl F).comp (archGLIncl F w) k₁))
      = archComponent F w (glArch (𝓞 F) F ((adelicArchGLIncl F).comp (archGLIncl F w) k₂)) at h1
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, glArch_adelicArchGLIncl, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_self, archComponent_archGLIncl_self] at h1
  exact Subtype.ext h1

end Ws31.T6d

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (u : AdelicGL2 (𝓞 K) K → ℂ) (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (tysK : ArchTypeFamily K) (_harch : IsArchBiFinite K tysK f) :
    convOp K f u ∈ archCutSubmodule K tysK := by
  classical
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

  have hloc : ∀ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C → IntegrableOn u C (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro C hC
    have hMem := AutomorphicForm.memLp_two_restrict_of_isCompact_of_isAutomorphicFnAt_canonicalTruncationDomain
      K α β hα hαβ ξK hξc u _hu C hC
    haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) :=
      isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
    exact hMem.integrable one_le_two

  have hint : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, Continuous h → HasCompactSupport h →
      Integrable (fun y => u y * h y) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro h hh hhc
    have h1 : IntegrableOn (fun y => u y * h y) (tsupport h) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
      (hloc _ hhc).mul_continuousOn hh.continuousOn hhc
    exact h1.integrable_of_forall_notMem_eq_zero fun y hy => by
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

  rw [AutomorphicForm.mem_archCutSubmodule_iff]
  intro w
  have hfw := (AutomorphicForm.mem_archCutSubmodule_iff K tysK _).mp _harch.1 w
  change convOp K f u ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ K w) (tysK.rep w i).ρ
  change (fun x => f x⁻¹) ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ K w) (tysK.rep w i).ρ at hfw
  rw [AutomorphicForm.mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero (rowIsometryInclAt₀ K w)
    (Ws31.T6d.rowIsometryInclAt₀_injective K w) (fun i => (tysK.rep w i).ρ)] at hfw ⊢
  intro a ha
  have h0 := hfw a ha
  funext x

  have e1 : ∀ k : rowIsometrySubgroup₀ w.Completion,
      convOp K f u (x * rowIsometryInclAt₀ K w k)
        = ∫ y, u y * f ((x * rowIsometryInclAt₀ K w k)⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro k
    show rightConv K u f (x * rowIsometryInclAt₀ K w k) = _
    rw [rightConv_apply]
    rw [← integral_mul_left_eq_self (fun y => u y * f ((x * rowIsometryInclAt₀ K w k)⁻¹ * y))
      (x * rowIsometryInclAt₀ K w k)]
    simp only [inv_mul_cancel_left]

  have h0x : ∀ y : AdelicGL2 (𝓞 K) K,
      (a.sum fun k c => c * f ((x * rowIsometryInclAt₀ K w k)⁻¹ * y)) = 0 := by
    intro y
    have := congrFun h0 (y⁻¹ * x)
    simp only [Pi.zero_apply] at this
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
  show (a.sum fun k c => c * convOp K f u (x * rowIsometryInclAt₀ K w k)) = 0
  simp only [e1, Finsupp.sum]
  calc (∑ k ∈ a.support, a k * ∫ y, u y * f ((x * rowIsometryInclAt₀ K w k)⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
      = ∑ k ∈ a.support, ∫ y, a k * (u y * f ((x * rowIsometryInclAt₀ K w k)⁻¹ * y)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul]
    _ = ∫ y, ∑ k ∈ a.support, a k * (u y * f ((x * rowIsometryInclAt₀ K w k)⁻¹ * y)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        rw [integral_finset_sum]
        intro k _
        refine (hint _ ?_ ?_).const_mul (a k)
        · exact _hf.comp (continuous_const.mul continuous_id)
        · have e : (fun y => f ((x * rowIsometryInclAt₀ K w k)⁻¹ * y)) = f ∘ (Homeomorph.mulLeft (x * rowIsometryInclAt₀ K w k)⁻¹) := rfl
          rw [e]
          exact _hfc.comp_homeomorph _
    _ = ∫ y, u y * (a.sum fun k c => c * f ((x * rowIsometryInclAt₀ K w k)⁻¹ * y)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        congr 1
        funext y
        rw [Finsupp.sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by simp only [h0x, mul_zero, integral_zero]

end S_AutomorphicForm_convOp_mem_archCutSubmodule_of_isArchBiFinite_of_isAutomorphicFnAt
end P2MW
export P2MW.S_AutomorphicForm_convOp_mem_archCutSubmodule_of_isArchBiFinite_of_isAutomorphicFnAt (solution)
