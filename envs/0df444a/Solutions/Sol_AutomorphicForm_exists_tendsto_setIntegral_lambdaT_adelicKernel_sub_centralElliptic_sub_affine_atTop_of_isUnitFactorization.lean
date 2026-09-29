-- Prove2me | solution 1 for AutomorphicForm.exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5b75b4dc-1089-58b6-afa0-d4d9cd88de4b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Theorems.Thm_AutomorphicForm_exists_forall_le_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
import Theorems.Thm_AutomorphicForm_exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell
import Theorems.Thm_AutomorphicForm_exists_tendsto_setIntegral_hyperbolicCell_sub_affine_atTop_of_isUnitFactorization
import Theorems.Thm_AutomorphicForm_exists_tendsto_setIntegral_unipotentCell_sub_affine_atTop_of_isUnitFactorization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.gl2Weyl_val FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk"
p2m_attr_erase "simp" "Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.cpowChar_apply_val AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hff : ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
      (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
      (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
      AutomorphicForm.IsUnitFactorization K S f fa ff fS) :
    ∃ ν μ : ℂ, Filter.Tendsto (fun R : ℝ =>
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
          (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (@AutomorphicForm.lambdaT _
              (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
              (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
              (fun y => AutomorphicForm.adelicKernel K f x y)
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      (∫ x in ΦK, (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      ((R : ℂ) * ν + μ)) Filter.atTop (nhds 0) := by
  have hff' : IsFactorizableTestFn K f := by
    obtain ⟨S, fa, ff, fS, hfa, hfin, -, -, -, hfeq⟩ := hff
    exact ⟨fa, ff, hfa, hfin, hfeq⟩
  obtain ⟨R₁, h1⟩ :=
    AutomorphicForm.exists_forall_le_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_eq_setIntegral_parabolic K α β hα hαβ ΦK hΦKs hΦK νZK ΩK hΩK ξ hξc hξt f hff'
  obtain ⟨R₂, h2⟩ :=
    AutomorphicForm.exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell K α β hα hαβ ΦK hΦKs hΦK νZK ΩK hΩK ξ hξc hξt f hff'
  obtain ⟨a₁, b₁, hH⟩ := AutomorphicForm.exists_tendsto_setIntegral_hyperbolicCell_sub_affine_atTop_of_isUnitFactorization K α β hα hαβ ΦK hΦKs hΦK νZK ΩK hΩK ξ hξc hξt f hff
  obtain ⟨a₂, b₂, hU⟩ := AutomorphicForm.exists_tendsto_setIntegral_unipotentCell_sub_affine_atTop_of_isUnitFactorization K α β hα hαβ ΦK hΦKs hΦK νZK ΩK hΩK ξ hξc hξt f hff

  have hH' : Filter.Tendsto (fun R : ℝ =>
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                  (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
                    Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                    (@AutomorphicForm.constantTerm _
                      (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                      (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                      (fun t => AutomorphicForm.unipotentGL2 t)
                      (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                        (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                          (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                        f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
                    (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                  ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      ((R : ℂ) * a₁ + b₁)) Filter.atTop (nhds 0) := hH
  have hU' : Filter.Tendsto (fun R : ℝ =>
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                  (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
                    Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                    (@AutomorphicForm.constantTerm _
                      (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                      (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                      (fun t => AutomorphicForm.unipotentGL2 t)
                      (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                        (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                          (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                        f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
                    (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                  ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      ((R : ℂ) * a₂ + b₂)) Filter.atTop (nhds 0) := hU
  refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
  have hsum := hH'.add hU'
  rw [add_zero] at hsum
  have key : ∀ R : ℝ, max R₁ R₂ ≤ R →
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                  (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
                    Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                    (@AutomorphicForm.constantTerm _
                      (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                      (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                      (fun t => AutomorphicForm.unipotentGL2 t)
                      (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                        (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                          (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                        f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
                    (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                  ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) +
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                  (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
                    Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                    (@AutomorphicForm.constantTerm _
                      (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                      (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                      (fun t => AutomorphicForm.unipotentGL2 t)
                      (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                        (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                          (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                        f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
                    (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                  ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
          (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (@AutomorphicForm.lambdaT _
              (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
              (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
              (fun y => AutomorphicForm.adelicKernel K f x y)
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      (∫ x in ΦK, (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
    intro R hR
    rw [h1 R (le_trans (le_max_left _ _) hR), (h2 R (le_trans (le_max_right _ _) hR)).2.2.2.2]
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (max R₁ R₂)] with R hR
  rw [← key R hR]
  simp only [Set.mem_setOf_eq, mul_add]
  abel

end S_AutomorphicForm_exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization
end P2MW
export P2MW.S_AutomorphicForm_exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization (solution)
