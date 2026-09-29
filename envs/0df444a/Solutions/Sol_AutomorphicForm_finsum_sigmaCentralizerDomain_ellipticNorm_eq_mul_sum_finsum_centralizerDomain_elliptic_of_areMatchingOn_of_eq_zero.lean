-- Prove2me | solution 1 for AutomorphicForm.finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_areMatchingOn_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a42f9838-1f22-59e3-91fd-00cf719a36d4

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_AutomorphicForm_setIntegral_mul_setIntegral_sigmaCentralizerDomain_eq_mul_sum_setIntegral_range_idelicNorm_of_normClassMap_eq_of_areMatchingOn
import Theorems.Thm_AutomorphicForm_finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_forall_perClass
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_areMatchingOn_of_eq_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.isMaximal_ratPrimeIdeal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.gl2Weyl_val NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk NumberField.FiniteSIdele.fibre_inr"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (RL : Set (GL (Fin 2) L))
    (hRLsub : RL ⊆ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ})
    (hRL : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
      ∃! δ₀ : GL (Fin 2) L, δ₀ ∈ RL ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h))
    (ΨL : GL (Fin 2) L → Set (AdelicGL2 (𝓞 L) L))
    (hΨLs : ∀ δ₀ ∈ RL, ΨL δ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨL : ∀ δ₀ ∈ RL, IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) (ΨL δ₀)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (RK : Set (GL (Fin 2) K))
    (hRKsub : RK ⊆ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K)
    (hRK : ∀ γ ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K, ∃! γ₀ : GL (Fin 2) K,
      γ₀ ∈ RK ∧ ∃ (h : GL (Fin 2) K) (a : Kˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))
    (ΨK : GL (Fin 2) K → Set (AdelicGL2 (𝓞 K) K))
    (hΨKs : ∀ γ₀ ∈ RK, ΨK γ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨK : ∀ γ₀ ∈ RK, IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K))
      (ΨK γ₀)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (c₀ : NNReal) (κ : ℝ) (hκ : 0 < κ)
    (hκl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        ENNReal.ofReal κ *
          ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hκi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
      (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
        IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
      ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        κ * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hOn : AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ.symm
      (@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
        (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
        (Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
        (adelicGLHaar (Fin 2) (𝓞 L) L))
      (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
      (φ ∘ Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
      f)
    (hvan : ∀ γ₀ ∈ RK, γ₀ ∈ AutomorphicForm.ellipticCell K → ∀ (a : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
      ¬ LT.TwistedNorm.IsNormClass hgen
          (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) →
      (∃ c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm
            (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
          AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
            (AutomorphicForm.centralScalar (𝓞 K) K u)) →
      ∀ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
          Set (AdelicGL2 (𝓞 K) K))), τ.IsHaarMeasure →
      ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K)
          (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u))
          τ f I → I = 0) :
    (RL ∩ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
          ConjClasses.mk γ} ∩
      Function.support (fun δ₀ : GL (Fin 2) L =>
        ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
            ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
              Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
                h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ *
          ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL)).Finite ∧
    (∀ ξK ∈ Ξ, (RK ∩ AutomorphicForm.ellipticCell K ∩
      Function.support (fun γ₀ : GL (Fin 2) K =>
        ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
            Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
          ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK)).Finite) ∧
    (∑ᶠ δ₀ ∈ RL ∩ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
          ConjClasses.mk γ},
      ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
              h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ *
        ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL) =
      (((c₀ : ℝ) * κ / ((Module.finrank K L : ℝ) * ((max 1 Ξ.card : ℕ) : ℝ)) : ℝ) : ℂ) *
        ∑ ξK ∈ Ξ, ∑ᶠ γ₀ ∈ RK ∩ AutomorphicForm.ellipticCell K,
          ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
              Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
            ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK := by
  refine AutomorphicForm.finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_forall_perClass K L hprime α β hα hαβ νZL D σ hσ hgen ξL hξc hξt Ξ hΞ νZK RL hRLsub hRL ΨL hΨLs hΨL Θ hΘ RK hRKsub hRK ΨK hΨKs hΨK c₀ κ hκ hκl hκi φ hφ hφc f hf hfc hOn hvan ?_
  intro δ₀ hδ₀ γ₀ hγ₀ hγ₀e a hN
  exact AutomorphicForm.setIntegral_mul_setIntegral_sigmaCentralizerDomain_eq_mul_sum_setIntegral_range_idelicNorm_of_normClassMap_eq_of_areMatchingOn K L hprime α β hα hαβ νZL D σ hσ hgen ξL hξc hξt Ξ hΞ νZK RL hRLsub hRL ΨL hΨLs hΨL Θ hΘ RK hRKsub hRK ΨK hΨKs hΨK c₀ κ hκ hκl hκi φ hφ hφc f hf hfc hOn hvan δ₀ hδ₀ γ₀ hγ₀ hγ₀e a hN

end S_AutomorphicForm_finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_areMatchingOn_of_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_areMatchingOn_of_eq_zero (solution)
