-- Prove2me | solution 1 for AutomorphicForm.integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6e15b7cd-e381-57ec-8128-70dd25cf058c

import Theorems.Thm_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_tsum_finsum_setIntegral_of_orthonormal_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm_eq_tsum_finsum_setIntegral_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_finsum_setIntegral_convOp_mul_conj_sigmaAdelicAct_symm_eq_twistedCutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_tsum_twistedCutTrace_eq_tsum_twistedCutTrace_principalLevel_mul_ideleNorm_det_rpow_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
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
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm
p2m_attr_erase "instance" "AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace R4CuspSwapSigma

theorem lambdaT_const_mul {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) (c : ℂ) (k : G → ℂ) (g : G) :
    AutomorphicForm.lambdaT μ u H T (fun y => c * k y) g = c * AutomorphicForm.lambdaT μ u H T k g := by
  have hct : AutomorphicForm.constantTerm μ u (fun y => c * k y) g =
      c * AutomorphicForm.constantTerm μ u k g := by
    simp only [AutomorphicForm.constantTerm, AutomorphicForm.constantTermIntegrand]
    exact integral_const_mul c _
  rw [AutomorphicForm.lambdaT_apply, AutomorphicForm.lambdaT_apply]
  by_cases h : g ∈ AutomorphicForm.highSet H T
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hct, mul_sub]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, sub_zero, sub_zero]

theorem finiteDimensional_of_span_eq {ι : Type*} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : ι → V) (s : Set ι) (hs : s.Finite) (W : Submodule ℂ V)
    (h : Submodule.span ℂ (b '' s) = W) : FiniteDimensional ℂ ↥W := by
  rw [← h]
  exact FiniteDimensional.span_of_finite ℂ (hs.image b)

end R4CuspSwapSigma

open AutomorphicForm R4CuspSwapSigma in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ))
    (ξ' : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξ' : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' ⟨z, Subgroup.mem_top z⟩ = ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩)
    (ξ₀ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξ₀ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL ∧
      b i ∈ isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL (cls i) ⊓ archCutSubmodule L tysL)
    (hb₁ : ∀ i, ∫ g in ΦL, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in ΦL, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0)
    (hbs : ∀ π ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π ⊓ archCutSubmodule L tysL)
    (hbc : ∀ ψ : AdelicGL2 (𝓞 L) L → ℂ,
      IsSmoothCuspAutomorphicFnAt L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL ψ →
      Continuous ψ →
      (∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).U N, ψ (g * k) = ψ g) →
      ψ ∈ archCutSubmodule L tysL →
      (∀ i, ∫ g in ΦL, ψ g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0) →
      ψ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL] 0)
    (ι' : Type) (b' : ι' → AdelicGL2 (𝓞 L) L → ℂ) (cls' : ι' → HeckeEigensystem L ℂ)
    (hb' : ∀ i, cls' i ∈ cuspClasses L
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ N SL ∧
        b' i ∈ isotypicCuspSubmodule L
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ N SL (cls' i) ⊓ archCutSubmodule L tysL)
    (hb'n : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain L α β,
        b' i g * conj (b' i g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 1)
    (hb'o : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain L α β,
        b' i g * conj (b' j g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0)
    (hb's : ∀ π ∈ cuspClasses L
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ N SL,
        {i | cls' i = π}.Finite ∧
        Submodule.span ℂ (b' '' {i | cls' i = π}) = isotypicCuspSubmodule L
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ N SL π ⊓ archCutSubmodule L tysL)
    (hb'c : ∀ ψ : AdelicGL2 (𝓞 L) L → ℂ,
        IsSmoothCuspAutomorphicFnAt L
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ ψ →
        Continuous ψ →
        (∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)).U N, ψ (g * u) = ψ g) →
        ψ ∈ archCutSubmodule L tysL →
        (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain L α β,
            ψ g * conj (b' i g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0) →
        ψ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 L) L).restrict (AutomorphicForm.canonicalTruncationDomain L α β)] 0)
    (φ φ' : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ' : ∀ g : AdelicGL2 (𝓞 L) L, φ' g = φ g *
      (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ))
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hfact : IsFactorizableTestFn L φ)
    (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (harch : IsArchBiFinite L tysL φ) :
    ∀ R : ℝ,
      IntegrableOn (fun x =>
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x)))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      IntegrableOn (fun x =>
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι', convOp L φ' (b' i) x * conj (b' i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀,
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x)) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (∫ x in Φ₀,
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι', convOp L φ' (b' i) x * conj (b' i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by
  intro R

  obtain ⟨-, -, -, hΦcs, hΦc⟩ :=
    AutomorphicForm.canonicalTruncationData_isTruncationDatum L α β hα hαβ

  have hbi₀ : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ :=
    AutomorphicForm.IsBiInvariantUnder.mono L
      (inf_le_inf_right (finiteAdelicGL2Subgroup L) (principalLevel_le_levelOne (𝓞 L) L N)) hbi
  have hφ'eq : φ' = fun g : AdelicGL2 (𝓞 L) L => φ g *
      (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ) :=
    funext hφ'
  obtain ⟨hTc, hTk, hTf, hTU, hTt⟩ :=
    AutomorphicForm.isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow
      L N tysL w φ hφ hφc hfact hbi₀ harch
  have hφ'c : Continuous φ' := by rw [hφ'eq]; exact hTc
  have hφ'k : HasCompactSupport φ' := by rw [hφ'eq]; exact hTk
  have hφ'f : IsFactorizableTestFn L φ' := by rw [hφ'eq]; exact hTf
  have hφ'U : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ' := by
    rw [hφ'eq]; exact hTU
  have hφ't : IsArchBiFinite L tysL φ' := by rw [hφ'eq]; exact hTt

  have hξ₀' : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) =
        ((ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
    intro z
    rw [hξ₀ z, hξ' z]

  have hfin₁ : ∀ Ψ ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
      FiniteDimensional ℂ ↥(isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ ⊓ archCutSubmodule L tysL) :=
    fun Ψ hΨ => finiteDimensional_of_span_eq b {i | cls i = Ψ} (hbs Ψ hΨ).1 _ (hbs Ψ hΨ).2
  have hfin₂ : ∀ Ψ ∈ cuspClasses L
        (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ N SL,
      FiniteDimensional ℂ ↥(isotypicCuspSubmodule L
        (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ N SL Ψ ⊓ archCutSubmodule L tysL) :=
    fun Ψ hΨ => finiteDimensional_of_span_eq b' {i | cls' i = Ψ} (hb's Ψ hΨ).1 _ (hb's Ψ hΨ).2

  obtain ⟨h1i, h1e⟩ :=
    AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_tsum_finsum_setIntegral_of_orthonormal_of_isFundamentalDomain_slab
      K L D σ α β hα hαβ ΦL hΦs hΦ ξL SL hSL N hN tysL Φ₀ hΦ₀s hΦ₀ ι b cls hb hb₁ hb₀ hbs φ hφ hφc hfact hbi harch R

  have h3 := fun Ψ : {Ψ : HeckeEigensystem L ℂ //
        Ψ ∈ cuspClasses L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL} =>
    AutomorphicForm.finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab
      K L D σ α β hα hαβ ΦL hΦs hΦ Φ₀ hΦ₀s hΦ₀ ξL SL hSL N hN tysL ι b cls hb hb₁ hb₀ hbs φ hφ hφc hbi harch Ψ.1 Ψ.2

  obtain ⟨h2i, h2e⟩ :=
    AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm_eq_tsum_finsum_setIntegral_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
      K L D σ α β hα hαβ (AutomorphicForm.canonicalTruncationDomain L α β) hΦcs hΦc ξ₀ SL hSL N hN tysL
      Φ₀ hΦ₀s hΦ₀ ι' b' cls' hb' hb'n hb'o hb's φ' hφ'c hφ'k hφ'f hφ'U hφ't R

  have h4 := fun Ψ : {Ψ : HeckeEigensystem L ℂ //
        Ψ ∈ cuspClasses L
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
            (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ₀ N SL} =>
    AutomorphicForm.finsum_setIntegral_convOp_mul_conj_sigmaAdelicAct_symm_eq_twistedCutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
      K L D σ α β hα hαβ (AutomorphicForm.canonicalTruncationDomain L α β) hΦcs hΦc ξ₀ SL hSL N hN tysL
      Φ₀ hΦ₀s hΦ₀ ι' b' cls' hb' hb'n hb'o hb's φ' hφ'c hφ'k hφ'U hφ't Ψ.1 Ψ.2

  have h5 :=
    AutomorphicForm.tsum_twistedCutTrace_eq_tsum_twistedCutTrace_principalLevel_mul_ideleNorm_det_rpow_of_isFundamentalDomain_slab
      K L D σ α β hα hαβ ΦL hΦs hΦ (AutomorphicForm.canonicalTruncationDomain L α β) hΦcs hΦc ξL SL hSL N hN tysL
      w ξ₀ hξ₀' φ hφ hφc hbi harch φ' hφ'c hφ'k hφ' hfin₁ hfin₂

  refine ⟨?_, ?_, ?_⟩
  ·
    simp only [lambdaT_const_mul]
    exact h1i.const_mul _
  ·
    simp only [lambdaT_const_mul]
    exact h2i.const_mul _
  ·
    simp only [lambdaT_const_mul]
    rw [integral_const_mul, integral_const_mul, h1e, tsum_congr h3, h5, ← tsum_congr h4]
    exact congrArg (fun t : ℂ => _ * t) h2e.symm

end S_AutomorphicForm_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm (solution)
