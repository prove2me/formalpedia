-- Prove2me | solution 1 for AutomorphicForm.setIntegral_twistedEllipticCentralFold_eq_const_mul_sum_of_factorization_of_normFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e55a42e3-15f4-5481-a2ac-1dd6dc711a31

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Mathlib
import Theorems.Thm_AutomorphicForm_setIntegral_twistedCentralEllipticFold_eq_finsum_inv_card_mul_setIntegral_sigmaCentralizerDomain
import Theorems.Thm_AutomorphicForm_setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization
import Theorems.Thm_AutomorphicForm_finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_areMatchingOn_of_eq_zero
import Theorems.Thm_AutomorphicForm_finsum_sigmaCentralizerDomain_centralNorm_eq_mul_sum_finsum_centralizerDomain_central_of_central_transfer
import Theorems.Thm_AutomorphicForm_isNormOf_map_of_isNormOf
import Theorems.Thm_AutomorphicForm_exists_areMatchingOn_adeleRing_of_areMatchingAt_of_prime
import Theorems.Thm_AutomorphicForm_isNormClass_mk_of_mem_ellipticCell_of_forall_isNormOf
import Theorems.Thm_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_setLIntegral_comp_idelicNorm_fundamentalDomain_eq_measure_mul_lintegral_haarQuotient_ker
import Theorems.Thm_NumberField_measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_twistedEllipticCentralFold_eq_const_mul_sum_of_factorization_of_normFibre
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.preimage_mulLeft_smul M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply"
p2m_attr_erase "simp" "Representation.normBar_mk AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj"
p2m_attr_erase "simp" "JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.cpowChar_apply_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt"
p2m_attr_erase "simp" "LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

namespace CM1Top
theorem secondCountableTopology_units (M : Type*) [Monoid M] [TopologicalSpace M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology
end CM1Top

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

namespace R4FafCu

section Transport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

noncomputable def transportEquiv : (L ⊗[K] AdeleRing (𝓞 K) K) ≃+* AdeleRing (𝓞 L) L :=
  ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
    (M4aHerbrand.Bridge.genuineRingEquiv K L))

theorem continuous_transportEquiv :
    Continuous (transportEquiv K L) ∧ Continuous (transportEquiv K L).symm := by
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  haveI : IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    M4aHerbrand.Bridge.isModuleTopology_adeleRing_of_free (𝓞 K) K (𝓞 L) L
      (M4aHerbrand.Bridge.continuous_genuineβ K L) (M4aHerbrand.Bridge.genuineTensorEquiv K L)
  let eLin : (L ⊗[K] AdeleRing (𝓞 K) K) ≃ₗ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L :=
    (TensorProduct.RightActions.Module.TensorProduct.comm K (AdeleRing (𝓞 K) K) L).symm.trans
      (M4aHerbrand.Bridge.genuineTensorEquiv K L).toLinearEquiv
  have hfun : ∀ x, eLin x = transportEquiv K L x := by
    intro x
    rfl
  let eC := IsModuleTopology.continuousLinearEquiv eLin
  have h1 : Continuous (transportEquiv K L) := by
    have : Continuous eC := eC.continuous
    exact this.congr hfun
  have h2 : Continuous (transportEquiv K L).symm := by
    have hc : Continuous eC.symm := eC.symm.continuous
    refine hc.congr fun y => ?_
    apply (transportEquiv K L).injective
    rw [RingEquiv.apply_symm_apply]
    show transportEquiv K L (eLin.symm y) = y
    rw [← hfun, LinearEquiv.apply_symm_apply]
  exact ⟨h1, h2⟩

noncomputable def glTransport :
    GL (Fin 2) (AdeleRing (𝓞 L) L) ≃* GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) where
  toFun := Matrix.GeneralLinearGroup.map (transportEquiv K L).symm.toRingHom
  invFun := Matrix.GeneralLinearGroup.map (transportEquiv K L).toRingHom
  left_inv g := by
    ext i j
    exact (transportEquiv K L).apply_symm_apply (g.val i j)
  right_inv g := by
    ext i j
    exact (transportEquiv K L).symm_apply_apply (g.val i j)
  map_mul' := map_mul _

theorem glTransport_apply (g : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
    glTransport K L g = Matrix.GeneralLinearGroup.map (transportEquiv K L).symm.toRingHom g := rfl

theorem coe_glTransport :
    ⇑(glTransport K L) = ⇑(Matrix.GeneralLinearGroup.map (transportEquiv K L).symm.toRingHom) := rfl

theorem glTransport_symm_apply (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    (glTransport K L).symm g = Matrix.GeneralLinearGroup.map (transportEquiv K L).toRingHom g := rfl

theorem continuous_generalLinearGroup_map {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Continuous.matrix_map Units.continuous_val hf
  · exact Continuous.matrix_map Units.continuous_coe_inv hf

theorem continuous_glTransport :
    Continuous (glTransport K L) ∧ Continuous (glTransport K L).symm := by
  obtain ⟨h1, h2⟩ := continuous_transportEquiv K L
  exact ⟨continuous_generalLinearGroup_map _ h2, continuous_generalLinearGroup_map _ h1⟩

noncomputable def glTransportC :
    GL (Fin 2) (AdeleRing (𝓞 L) L) ≃ₜ* GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  { glTransport K L with
    continuous_toFun := (continuous_glTransport K L).1
    continuous_invFun := (continuous_glTransport K L).2 }

theorem coe_glTransportC :
    ⇑(glTransportC K L) = ⇑(Matrix.GeneralLinearGroup.map (transportEquiv K L).symm.toRingHom) := rfl

theorem isHaarMeasure_map_transport :
    @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
      (@Measure.map (GL (Fin 2) (AdeleRing (𝓞 L) L)) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
        (glBorel (Fin 2) (𝓞 L) L) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
        (Matrix.GeneralLinearGroup.map (transportEquiv K L).symm.toRingHom)
        (adelicGLHaar (Fin 2) (𝓞 L) L)) := by
  letI := glBorel (Fin 2) (𝓞 L) L
  haveI := borelSpace_glBorel (Fin 2) (𝓞 L) L
  letI := AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.t2Space_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  rw [← coe_glTransportC]
  exact (glTransportC K L).isHaarMeasure_map (adelicGLHaar (Fin 2) (𝓞 L) L)

end Transport

section Cells

variable {K : Type*} [Field K]

theorem not_isEllipticType_smul_one (c : K) :
    ¬ AutomorphicForm.IsEllipticType (c • (1 : Matrix (Fin 2) (Fin 2) K)) := by
  intro h
  apply h c
  rw [Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp [Polynomial.IsRoot]

theorem not_mem_ellipticCell_of_mem_centralCell {γ : GL (Fin 2) K}
    (hγ : γ ∈ AutomorphicForm.centralCell K) : γ ∉ AutomorphicForm.ellipticCell K := by
  obtain ⟨c, hc⟩ := hγ
  intro hell
  rw [AutomorphicForm.mem_ellipticCell_iff, hc] at hell
  exact not_isEllipticType_smul_one c hell

theorem disjoint_centralCell_ellipticCell (K : Type*) [Field K] :
    Disjoint (AutomorphicForm.centralCell K) (AutomorphicForm.ellipticCell K) :=
  Set.disjoint_left.mpr fun _ hγ => not_mem_ellipticCell_of_mem_centralCell hγ

theorem eq_of_isConj_of_mem_centralCell {γ γ' : GL (Fin 2) K} (h : IsConj γ γ')
    (hγ' : γ' ∈ AutomorphicForm.centralCell K) : γ = γ' := by
  obtain ⟨c, hc⟩ := hγ'
  obtain ⟨P, hP⟩ := isConj_iff.mp h

  have : γ = P⁻¹ * γ' * P := by rw [← hP]; group
  rw [this]
  exact LT.TwistedNorm.GL2.conj_eq_self_of_coe_eq_smul_one γ' P c hc

theorem not_mem_ellipticCell_of_mk_eq_mk {γ γ' : GL (Fin 2) K}
    (h : ConjClasses.mk γ = ConjClasses.mk γ') (hγ' : γ' ∈ AutomorphicForm.centralCell K) :
    γ ∉ AutomorphicForm.ellipticCell K := by
  have := eq_of_isConj_of_mem_centralCell (ConjClasses.mk_eq_mk_iff_isConj.mp h) hγ'
  subst this
  exact not_mem_ellipticCell_of_mem_centralCell hγ'

theorem subsingleton_inter_centralCell (RK : Set (GL (Fin 2) K))
    (hRK : ∀ γ ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K, ∃! γ₀ : GL (Fin 2) K,
      γ₀ ∈ RK ∧ ∃ (h : GL (Fin 2) K) (a : Kˣ),
        γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h)) :
    (RK ∩ AutomorphicForm.centralCell K).Subsingleton := by
  rintro γ₁ ⟨h₁R, c₁, hc₁⟩ γ₂ ⟨h₂R, c₂, hc₂⟩

  have hc₁0 : c₁ ≠ 0 := by
    intro h0
    have hdet := γ₁.isUnit.ne_zero
    apply (Matrix.isUnits_det_units γ₁).ne_zero
    rw [hc₁, h0, zero_smul, Matrix.det_zero]
  have hc₂0 : c₂ ≠ 0 := by
    intro h0
    apply (Matrix.isUnits_det_units γ₂).ne_zero
    rw [hc₂, h0, zero_smul, Matrix.det_zero]
  obtain ⟨γ₀, -, huniq⟩ := hRK γ₂ (Or.inl ⟨c₂, hc₂⟩)
  have e₂ : γ₂ = γ₀ := huniq γ₂ ⟨h₂R, 1, 1, by simp⟩
  have e₁ : γ₁ = γ₀ := by
    refine huniq γ₁ ⟨h₁R, 1, Units.mk0 (c₂ / c₁) (div_ne_zero hc₂0 hc₁0), ?_⟩
    apply Units.ext
    simp only [Units.val_mul, inv_one, one_mul, mul_one]
    rw [hc₂, hc₁]
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_apply, Matrix.one_apply, div_mul_cancel₀ _ hc₁0]
  rw [e₁, e₂]

end Cells

section Assembly

theorem assemble {ι ι' X : Type*} (RL PE PC : Set ι) (RK CC CE : Set ι') (Ξ : Finset X)
    (F : ι → ℂ) (G : X → ι' → ℂ) (c : ℂ)
    (hRL : RL ⊆ PE ∪ PC) (hdisj : Disjoint PE PC) (hRK : RK ⊆ CC ∪ CE) (hdisjK : Disjoint CC CE)
    (hfinE : (RL ∩ PE ∩ Function.support F).Finite) (hfinC : (RL ∩ PC ∩ Function.support F).Finite)
    (hfinKC : ∀ ξ ∈ Ξ, (RK ∩ CC ∩ Function.support (G ξ)).Finite)
    (hfinKE : ∀ ξ ∈ Ξ, (RK ∩ CE ∩ Function.support (G ξ)).Finite)
    (hE : ∑ᶠ i ∈ RL ∩ PE, F i = c * ∑ ξ ∈ Ξ, ∑ᶠ j ∈ RK ∩ CE, G ξ j)
    (hC : ∑ᶠ i ∈ RL ∩ PC, F i = c * ∑ ξ ∈ Ξ, ∑ᶠ j ∈ RK ∩ CC, G ξ j) :
    ∑ᶠ i ∈ RL, F i = c * ∑ ξ ∈ Ξ, ∑ᶠ j ∈ RK, G ξ j := by
  have hRLeq : RL = (RL ∩ PE) ∪ (RL ∩ PC) := by
    rw [← Set.inter_union_distrib_left, Set.inter_eq_left.mpr hRL]
  have hRKeq : RK = (RK ∩ CC) ∪ (RK ∩ CE) := by
    rw [← Set.inter_union_distrib_left, Set.inter_eq_left.mpr hRK]
  have hdL : Disjoint (RL ∩ PE) (RL ∩ PC) :=
    hdisj.mono Set.inter_subset_right Set.inter_subset_right
  have hdK : Disjoint (RK ∩ CC) (RK ∩ CE) :=
    hdisjK.mono Set.inter_subset_right Set.inter_subset_right
  have hK : ∀ ξ ∈ Ξ, ∑ᶠ j ∈ RK, G ξ j = (∑ᶠ j ∈ RK ∩ CC, G ξ j) + ∑ᶠ j ∈ RK ∩ CE, G ξ j := by
    intro ξ hξ
    conv_lhs => rw [hRKeq]
    exact finsum_mem_union' hdK (hfinKC ξ hξ) (hfinKE ξ hξ)
  conv_lhs => rw [hRLeq]
  rw [finsum_mem_union' hdL hfinE hfinC, hE, hC, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ξ hξ => ?_
  rw [hK ξ hξ, add_comm]

end Assembly

section Scalars

variable {n : Type*} [DecidableEq n] [Fintype n]

theorem scalar_mul_comm {A : Type*} [CommRing A] (c : Aˣ) (x : GL n A) :
    Matrix.GeneralLinearGroup.scalar n c * x = x * Matrix.GeneralLinearGroup.scalar n c := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  exact (Matrix.scalar_commute (c : A) (fun r' => Commute.all _ _) (x : Matrix n n A)).eq

theorem map_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (c : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar n c) =
      Matrix.GeneralLinearGroup.scalar n (Units.map (f : A →* B) c) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map, MonoidHom.coe_coe]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem list_prod_comm_of_forall {G : Type*} [Monoid G] (l : List G)
    (h : ∀ z ∈ l, ∀ x : G, z * x = x * z) (x : G) : l.prod * x = x * l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons, mul_assoc, ih (fun z hz => h z (List.mem_cons_of_mem a hz)), ← mul_assoc,
      h a List.mem_cons_self, mul_assoc]

theorem list_prod_map_mul_of_comm {ι G : Type*} [Monoid G] (l : List ι) (f g : ι → G)
    (hg : ∀ i ∈ l, ∀ x : G, g i * x = x * g i) :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih (fun i hi => hg i (List.mem_cons_of_mem a hi))]
    have hc : (t.map f).prod * g a = g a * (t.map f).prod := (hg a List.mem_cons_self _).symm

    rw [mul_assoc (f a) (g a), ← mul_assoc (g a), ← hc]
    simp only [mul_assoc]

end Scalars

section NormString

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem iterate_sigmaGL_scalar (i : ℕ) (c : (L ⊗[K] A)ˣ) :
    ∃ c' : (L ⊗[K] A)ˣ, (⇑(AutomorphicForm.sigmaGL K L A σ))^[i]
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = Matrix.GeneralLinearGroup.scalar (Fin 2) c' := by
  induction i with
  | zero => exact ⟨c, rfl⟩
  | succ i ih =>
    obtain ⟨c', hc'⟩ := ih
    refine ⟨Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A) c', ?_⟩
    rw [Function.iterate_succ_apply', hc']
    exact map_scalar _ _

theorem iterate_sigmaGL_scalar_comm (i : ℕ) (c : (L ⊗[K] A)ˣ) (x : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * x =
      x * (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  obtain ⟨c', hc'⟩ := iterate_sigmaGL_scalar K L A σ i c
  rw [hc']
  exact scalar_mul_comm c' x

theorem normString_mul_scalar (δ : GL (Fin 2) (L ⊗[K] A)) (c : (L ⊗[K] A)ˣ) :
    AutomorphicForm.normString K L A σ (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.normString K L A σ δ *
        AutomorphicForm.normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  unfold AutomorphicForm.normString
  have hmul : ∀ i : ℕ, (⇑(AutomorphicForm.sigmaGL K L A σ))^[i]
      (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ *
        (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] (Matrix.GeneralLinearGroup.scalar (Fin 2) c) :=
    fun i => iterate_map_mul (AutomorphicForm.sigmaGL K L A σ) i δ _
  simp_rw [hmul]
  exact list_prod_map_mul_of_comm _ _ _ (fun i _ x => iterate_sigmaGL_scalar_comm K L A σ i c x)

theorem normString_one : AutomorphicForm.normString K L A σ 1 = 1 := by
  unfold AutomorphicForm.normString
  have : ∀ i : ℕ, (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] (1 : GL (Fin 2) (L ⊗[K] A)) = 1 :=
    fun i => iterate_map_one (AutomorphicForm.sigmaGL K L A σ) i
  simp_rw [this]
  simp

theorem normString_scalar_comm (c : (L ⊗[K] A)ˣ) (x : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * x =
      x * AutomorphicForm.normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  unfold AutomorphicForm.normString
  refine list_prod_comm_of_forall _ (fun z hz y => ?_) x
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
  exact iterate_sigmaGL_scalar_comm K L A σ i c y

theorem normString_scalar_inv (c : (L ⊗[K] A)ˣ) :
    AutomorphicForm.normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹) =
      (AutomorphicForm.normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c))⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  have h := normString_mul_scalar K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹) c
  rw [← map_mul, inv_mul_cancel, map_one, normString_one] at h
  exact h.symm

theorem isNormOf_of_isNormOf_mul_normString_scalar (γ : GL (Fin 2) A) (c : (L ⊗[K] A)ˣ)
    (δ y : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.toTensorGL K L A γ *
        AutomorphicForm.normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      y⁻¹ * AutomorphicForm.normString K L A σ δ * y) :
    AutomorphicForm.IsNormOf K L A σ γ (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹) := by
  refine ⟨y, ?_⟩
  unfold AutomorphicForm.IsNormConjugator
  rw [normString_mul_scalar, normString_scalar_inv]
  set Nc := AutomorphicForm.normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  have hcomm := normString_scalar_comm K L A σ c

  have h1 : AutomorphicForm.toTensorGL K L A γ = y⁻¹ * AutomorphicForm.normString K L A σ δ * y * Nc⁻¹ := by
    rw [← h, mul_inv_cancel_right]
  have h2 : y * Nc⁻¹ = Nc⁻¹ * y := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hcomm y, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1, mul_assoc (y⁻¹ * _) y, h2, ← mul_assoc, mul_assoc y⁻¹]

end NormString

section Regular

theorem isRegularSemisimple_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {g : GL (Fin 2) A} (hg : AutomorphicForm.IsRegularSemisimple g) :
    AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.map f g) := by
  unfold AutomorphicForm.IsRegularSemisimple at hg ⊢
  have := hg.map f
  simp only [map_sub, map_pow, map_mul, map_ofNat] at this
  convert this using 2
  · rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add, Matrix.GeneralLinearGroup.map_apply,
      Matrix.GeneralLinearGroup.map_apply]
  · rw [Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [map_sub, map_mul, Matrix.GeneralLinearGroup.map_apply]

theorem isRegularSemisimple_mul_scalar {A : Type*} [CommRing A] {g : GL (Fin 2) A}
    (hg : AutomorphicForm.IsRegularSemisimple g) (z : Aˣ) :
    AutomorphicForm.IsRegularSemisimple (g * Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  unfold AutomorphicForm.IsRegularSemisimple at hg ⊢
  have key : Matrix.trace ((g * Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A) ^ 2 -
      4 * Matrix.det ((g * Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A) =
      (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A)) *
        (z : A) ^ 2 := by
    have hval : ((g * Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A) = (z : A) • (g : Matrix (Fin 2) (Fin 2) A) := by
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      ext i j
      simp [Matrix.mul_diagonal, mul_comm]
    rw [hval, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin, smul_eq_mul]
    ring
  rw [key]
  exact hg.mul ((Units.isUnit z).pow 2)

end Regular

section Elliptic

variable {K : Type*} [Field K]

theorem isRegularSemisimple_of_mem_ellipticCell (h2 : (2 : K) ≠ 0) {γ : GL (Fin 2) K}
    (hγ : γ ∈ AutomorphicForm.ellipticCell K) : AutomorphicForm.IsRegularSemisimple γ := by
  rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero]
  intro hdisc
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  apply hγ (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) K) / 2)
  rw [Polynomial.IsRoot, Matrix.charpoly_fin_two]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C]
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two] at hdisc ⊢
  set s : K := ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 + (γ : Matrix (Fin 2) (Fin 2) K) 1 1) / 2 with hs
  have key : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 + (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 2 * s := by
    rw [hs]; field_simp
  rw [key] at hdisc ⊢
  have hP : (4 : K) * (s ^ 2 - ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 * (γ : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) K) 0 1 * (γ : Matrix (Fin 2) (Fin 2) K) 1 0)) = 0 := by
    linear_combination hdisc
  rcases mul_eq_zero.mp hP with h | h
  · exact absurd h h4
  · linear_combination (-1 : K) * h

theorem scalar_mul_mem_ellipticCell (a : Kˣ) {γ : GL (Fin 2) K}
    (hγ : γ ∈ AutomorphicForm.ellipticCell K) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ ∈ AutomorphicForm.ellipticCell K := by
  rw [AutomorphicForm.mem_ellipticCell_iff] at hγ ⊢
  intro r hr
  apply hγ (r / a)
  have hval : ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = (a : K) • (γ : Matrix (Fin 2) (Fin 2) K) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i j
    simp [Matrix.diagonal_mul]
  rw [hval] at hr
  rw [Polynomial.IsRoot, Matrix.charpoly_fin_two] at hr ⊢
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin,
    smul_eq_mul] at hr ⊢
  have ha : (a : K) ≠ 0 := a.ne_zero
  have key : (r / a) ^ 2 - Matrix.trace (γ : Matrix (Fin 2) (Fin 2) K) * (r / a) +
      Matrix.det (γ : Matrix (Fin 2) (Fin 2) K) =
      (r ^ 2 - (a : K) * Matrix.trace (γ : Matrix (Fin 2) (Fin 2) K) * r +
        (a : K) ^ 2 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) K)) / (a : K) ^ 2 := by
    field_simp
  rw [key, hr, zero_div]

end Elliptic

section Vanishing

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

noncomputable def toPlace (v : HeightOneSpectrum (𝓞 K)) :
    AdeleRing (𝓞 K) K →ₐ[K] v.adicCompletion K :=
  { (AdelicLevel.finAdeleEval (𝓞 K) K v).comp (AdelicLevel.adeleFin (𝓞 K) K) with
    commutes' := fun k => by
      show ((algebraMap K (AdeleRing (𝓞 K) K) k).2) v = algebraMap K (v.adicCompletion K) k
      rw [NumberField.AdeleRing.algebraMap_snd_apply, HeightOneSpectrum.algebraMap_adicCompletion]
      rfl }

noncomputable def toArch : AdeleRing (𝓞 K) K →ₐ[K] InfiniteAdeleRing K :=
  { AdelicLevel.adeleArch (𝓞 K) K with
    commutes' := fun k => rfl }

theorem toPlace_comp_algebraMap (v : HeightOneSpectrum (𝓞 K)) :
    (toPlace K v).toRingHom.comp (algebraMap K (AdeleRing (𝓞 K) K)) =
      algebraMap K (v.adicCompletion K) :=
  (toPlace K v).comp_algebraMap

theorem toArch_comp_algebraMap :
    (toArch K).toRingHom.comp (algebraMap K (AdeleRing (𝓞 K) K)) = algebraMap K (InfiniteAdeleRing K) :=
  (toArch K).comp_algebraMap

theorem globalPoints_scalar (a : Kˣ) :
    AutomorphicForm.globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      AutomorphicForm.centralScalar (𝓞 K) K
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) :=
  map_scalar _ _

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem orbitalIntegral_eq_zero_of_not_isNormClass
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (μK : Measure (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hOn2 : ∀ γ : AutomorphicForm.AdelicGL2 (𝓞 K) K, AutomorphicForm.IsRegularSemisimple γ →
      (¬ ∃ δ, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ γ δ) →
      ∀ τ : Measure (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
        τ.IsHaarMeasure →
        ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μK γ τ f I → I = 0)
    (hLG : ∀ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K →
      (∀ v : HeightOneSpectrum (𝓞 K), ∃ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) γ) δv) →
      (∃ δa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
        AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ
          (Matrix.GeneralLinearGroup.map (algebraMap K (InfiniteAdeleRing K)) γ) δa) →
      LT.TwistedNorm.IsNormClass hgen (ConjClasses.mk γ))
    (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K)
    (a : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hnot : ¬ LT.TwistedNorm.IsNormClass hgen
      (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)))
    (hc : ∃ c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
        AutomorphicForm.centralScalar (𝓞 K) K
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
        Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    (hτ : τ.IsHaarMeasure) (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μK
      (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
        AutomorphicForm.centralScalar (𝓞 K) K
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)) τ f I) :
    I = 0 := by
  set γ₁ : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ with hγ₁

  have he : AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
      AutomorphicForm.centralScalar (𝓞 K) K
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u) =
      AutomorphicForm.globalPoints (𝓞 K) K γ₁ * AutomorphicForm.centralScalar (𝓞 K) K u := by
    rw [hγ₁, map_mul (AutomorphicForm.globalPoints (𝓞 K) K), globalPoints_scalar,
      map_mul (AutomorphicForm.centralScalar (𝓞 K) K), ← mul_assoc]
    congr 1
    exact (scalar_mul_comm _ _).symm
  have hγ₁e : γ₁ ∈ AutomorphicForm.ellipticCell K := scalar_mul_mem_ellipticCell a hγ₀
  refine hOn2 _ ?_ ?_ τ hτ I hI
  ·
    rw [he]
    unfold AutomorphicForm.globalPoints AutomorphicForm.centralScalar
    exact isRegularSemisimple_mul_scalar
      (isRegularSemisimple_map _ (isRegularSemisimple_of_mem_ellipticCell two_ne_zero hγ₁e)) u
  ·
    rw [he]
    rintro ⟨δ, y, hy⟩
    obtain ⟨c, hc⟩ := hc
    apply hnot

    have hN : AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.globalPoints (𝓞 K) K γ₁)
        (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹) := by
      apply isNormOf_of_isNormOf_mul_normString_scalar K L (AdeleRing (𝓞 K) K) σ _ c δ y
      rw [hc, ← map_mul]
      exact hy
    refine hLG γ₁ hγ₁e (fun v => ?_) ?_
    · have h := AutomorphicForm.isNormOf_map_of_isNormOf K L (AdeleRing (𝓞 K) K) (v.adicCompletion K)
        (toPlace K v) σ _ _ hN
      rw [AutomorphicForm.globalPoints, ← Matrix.GeneralLinearGroup.map_comp_apply,
        ← Matrix.GeneralLinearGroup.map_comp, toPlace_comp_algebraMap] at h
      exact ⟨_, h⟩
    · have h := AutomorphicForm.isNormOf_map_of_isNormOf K L (AdeleRing (𝓞 K) K) (InfiniteAdeleRing K)
        (toArch K) σ _ _ hN
      rw [AutomorphicForm.globalPoints, ← Matrix.GeneralLinearGroup.map_comp_apply,
        ← Matrix.GeneralLinearGroup.map_comp, toArch_comp_algebraMap] at h
      exact ⟨_, h⟩

end Vanishing

end R4FafCu

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open AutomorphicForm (AdelicGL2)

theorem d10_explicit
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
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
    (hLG : ∀ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K →
      (∀ v : HeightOneSpectrum (𝓞 K), ∃ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ.symm
          (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) γ) δv) →
      (∃ δa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
        AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ.symm
          (Matrix.GeneralLinearGroup.map (algebraMap K (InfiniteAdeleRing K)) γ) δa) →
      LT.TwistedNorm.IsNormClass hgen (ConjClasses.mk γ))
    (hEuler : ∀ (μL : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
        (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))),
      @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
        (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μL →
      ∃ c₀ : NNReal, c₀ ≠ 0 ∧
        ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
        ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ),
          AutomorphicForm.AreMatchingAt K L σ.symm S' φ f →
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
            (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
              Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
            AutomorphicForm.AreMatchingLocal K L v σ.symm
              ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
              ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) →
          AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ.symm μL
            (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
            (φ ∘ Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
            f)
    (cK cL : ℝ) (hcK : 0 < cK) (hcL : 0 < cL)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa (AutomorphicForm.archHaarK K) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v) (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈ AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉ AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = cK * (∫ x, fa x ∂(AutomorphicForm.archHaarK K)) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (hG' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (F : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (FS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] Fa (AutomorphicForm.archHaarL K L) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (FS v) (AutomorphicForm.semiLocalHaar K L v)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = Fa (AutomorphicForm.tensorArch K L x) * ∏ v ∈ S, FS v (AutomorphicForm.tensorPlace K L v x)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) → F x = 0) →
          ∫ x, F x ∂(@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) (Matrix.GeneralLinearGroup.map (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom)) (adelicGLHaar (Fin 2) (𝓞 L) L)) = cL * (∫ y, Fa y ∂(AutomorphicForm.archHaarL K L)) * ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))
    (c₀ : NNReal) (hc₀ : (c₀ : ℝ) * cK = cL)
    (κ : ℝ) (hκ : 0 < κ)
    (hκl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        ENNReal.ofReal κ *
          ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hκi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
      (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
        IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
      ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        κ * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK) :
    ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
    ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ)
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
      (_hm : AutomorphicForm.AreMatchingAt K L σ.symm S' φ f)
      (_hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
        (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
          Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
        AutomorphicForm.AreMatchingLocal K L v σ.symm
          ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))),
      (∑ᶠ δ₀ ∈ RL,
        ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
            ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
              Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
                h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ *
          ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL) =
      (((c₀ : ℝ) * κ / ((Module.finrank K L : ℝ) * ((max 1 Ξ.card : ℕ) : ℝ)) : ℝ) : ℂ) * ∑ ξK ∈ Ξ, ∑ᶠ γ₀ ∈ RK,
        ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
            Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
          ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK := by
  classical

  have hHaar := R4FafCu.isHaarMeasure_map_transport K L
  have hσ' : σ.symm ≠ 1 := by
    intro h
    apply hσ
    have : σ = σ.symm.symm := (AlgEquiv.symm_symm σ).symm
    rw [this, h]
    rfl
  have hboth :=
    AutomorphicForm.areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization
      K L hprime σ.symm hσ' SK hS _ hHaar cK cL hcK hcL hG hG' c₀ hc₀

  have hℓ : 0 < (Module.finrank K L : ℝ) := by exact_mod_cast hprime.pos
  have hmax : 0 < ((max 1 Ξ.card : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (le_max_left 1 Ξ.card))
  have hc₀' : 0 < (c₀ : ℝ) := by
    have h1 : (c₀ : ℝ) * cK = cL := hc₀
    nlinarith [hcK, hcL, NNReal.coe_nonneg c₀]
  intro S' hS' φ hφ hφc f hf hfc hm hunit
  obtain ⟨hOn, hcent, hcvan⟩ := hboth S' hS' φ f hm hunit

  have hvan : ∀ γ₀ ∈ RK, γ₀ ∈ AutomorphicForm.ellipticCell K → ∀ (a : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
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
          τ f I → I = 0 :=
    fun γ₀ _ hγ₀e a u hnot hc τ hτ I hI =>
      R4FafCu.orbitalIntegral_eq_zero_of_not_isNormClass K L σ.symm hgen _ f hOn.2 hLG γ₀ hγ₀e a u
        hnot hc τ hτ I hI

  obtain ⟨hfinLE, hfinKE, hE⟩ :=
    AutomorphicForm.finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_areMatchingOn_of_eq_zero
      K L hprime α β hα hαβ νZL D σ hσ hgen ξL hξc hξt Ξ hΞ νZK RL hRLsub hRL ΨL hΨLs hΨL Θ hΘ
      RK hRKsub hRK ΨK hΨKs hΨK c₀ κ hκ hκl hκi φ hφ hφc f hf hfc hOn hvan
  obtain ⟨hfinLC, hC⟩ :=
    AutomorphicForm.finsum_sigmaCentralizerDomain_centralNorm_eq_mul_sum_finsum_centralizerDomain_central_of_central_transfer
      K L hprime α β hα hαβ νZL D σ hσ hgen ξL hξc hξt Ξ hΞ νZK RL hRLsub hRL ΨL hΨLs hΨL Θ hΘ
      RK hRKsub hRK ΨK hΨKs hΨK c₀ κ hκ hκl hκi φ hφ hφc f hf hfc hcent hcvan

  have hRL' : RL ⊆
      {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
            ConjClasses.mk γ} ∪
      {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.centralCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
            ConjClasses.mk γ} := by
    intro δ hδ
    obtain ⟨γ, hγ | hγ, hN⟩ := hRLsub hδ
    · exact Or.inl ⟨γ, hγ, hN⟩
    · exact Or.inr ⟨γ, hγ, hN⟩
  have hdisj : Disjoint
      {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
            ConjClasses.mk γ}
      {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.centralCell K ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
            ConjClasses.mk γ} := by
    refine Set.disjoint_left.mpr ?_
    rintro δ ⟨γ, hγ, hN⟩ ⟨γ', hγ', hN'⟩
    exact R4FafCu.not_mem_ellipticCell_of_mk_eq_mk (hN.symm.trans hN') hγ' hγ
  have hRK' : RK ⊆ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K := hRKsub
  have hfinKC : ∀ ξK ∈ Ξ, (RK ∩ AutomorphicForm.centralCell K ∩
      Function.support (fun γ₀ : GL (Fin 2) K =>
        ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
            Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
          ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK)).Finite :=
    fun ξK _ => ((R4FafCu.subsingleton_inter_centralCell RK hRK).finite).subset Set.inter_subset_left

  exact R4FafCu.assemble RL _ _ RK (AutomorphicForm.centralCell K) (AutomorphicForm.ellipticCell K) Ξ
    _ _ _ hRL' hdisj hRK' (R4FafCu.disjoint_centralCell_ellipticCell K) hfinLE hfinLC hfinKC hfinKE hE hC

set_option autoImplicit false

open MeasureTheory Set
open scoped Pointwise

namespace R2FafR

theorem exists_representatives {X : Type*} (I : Set X) (r : X → X → Prop)
    (hrefl : ∀ x, r x x) (hsymm : ∀ x y, r x y → r y x)
    (htrans : ∀ x y z, r x y → r y z → r x z) :
    ∃ R : Set X, R ⊆ I ∧ ∀ x ∈ I, ∃! x₀, x₀ ∈ R ∧ r x x₀ := by
  classical
  let s : Setoid I := ⟨fun a b => r a.1 b.1, ⟨fun a => hrefl a.1, fun h => hsymm _ _ h,
    fun h₁ h₂ => htrans _ _ _ h₁ h₂⟩⟩
  refine ⟨Set.range fun q : Quotient s => ((q.out : I) : X), ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact (q.out).2
  · intro x hx
    refine ⟨((⟦⟨x, hx⟩⟧ : Quotient s).out : I), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · have h : s (⟦(⟨x, hx⟩ : I)⟧ : Quotient s).out ⟨x, hx⟩ := Quotient.mk_out _
      exact hsymm _ _ h
    · rintro y ⟨⟨q, rfl⟩, hy⟩
      have h1 : s ⟨x, hx⟩ q.out := hy
      have h2 : (⟦(⟨x, hx⟩ : I)⟧ : Quotient s) = ⟦q.out⟧ := Quotient.sound h1
      rw [Quotient.out_eq] at h2
      rw [← h2]

theorem isFundamentalDomain_of_bijective {G H α : Type*} [Group G] [Group H] [MulAction G α]
    [MulAction H α] [MeasurableSpace α] {s : Set α} {μ : Measure α}
    (h : IsFundamentalDomain G s μ) (e : G → H) (he : Function.Bijective e)
    (hef : ∀ (g : G) (x : α), e g • x = g • x) : IsFundamentalDomain H s μ := by
  have := h.preimage_of_equiv (f := id) (ν := μ) (Measure.QuasiMeasurePreserving.id μ) he
    (fun g x => by simp [hef])
  simpa using this

scoped instance smulInvariantMeasure_top {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (Γ : Subgroup G) [SMulInvariantMeasure Γ α μ] :
    SMulInvariantMeasure (⊤ : Subgroup Γ) α μ :=
  ⟨fun g _ hs => SMulInvariantMeasure.measure_preimage_smul (μ := μ) (g : Γ) hs⟩

theorem exists_isFundamentalDomain_subgroup {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] [MeasurableSpace G] [MeasurableSMul G α]
    (μ : Measure α) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [SMulInvariantMeasure Γ₁ α μ] (𝓕 : Set α) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ) :
    ∃ Ψ : Set α, IsFundamentalDomain Γ₂ Ψ μ ∧ Ψ ⊆ ⋃ γ : Γ₁, (γ : G) • 𝓕 := by
  classical

  let Γ₂' : Subgroup Γ₁ := Γ₂.subgroupOf Γ₁
  have h𝓕' : IsFundamentalDomain (⊤ : Subgroup Γ₁) 𝓕 μ :=
    isFundamentalDomain_of_bijective h𝓕 (fun g : Γ₁ => (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup Γ₁)))
      ⟨fun a b hab => by simpa using congrArg Subtype.val hab, fun g => ⟨g.1, rfl⟩⟩ (fun _ _ => rfl)
  let ι := Γ₁ ⧸ Γ₂'
  let R : ι → (⊤ : Subgroup Γ₁) := fun q => ⟨q.out, Subgroup.mem_top _⟩
  have hR : ∀ γ : (⊤ : Subgroup Γ₁), ∃! i, ((R i)⁻¹ * γ : Γ₁) ∈ Γ₂' := by
    intro γ
    refine ⟨(QuotientGroup.mk (γ : Γ₁) : ι), ?_, ?_⟩
    · change ((QuotientGroup.mk (γ : Γ₁) : ι).out)⁻¹ * (γ : Γ₁) ∈ Γ₂'
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    · intro i hi
      change (i.out)⁻¹ * (γ : Γ₁) ∈ Γ₂' at hi
      rw [← QuotientGroup.eq, QuotientGroup.out_eq'] at hi
      exact hi
  haveI : Countable (⊤ : Subgroup Γ₁) := inferInstance
  haveI : Countable ι := Quotient.countable
  have hfd := MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
    μ (⊤ : Subgroup Γ₁) Γ₂' le_top 𝓕 h𝓕' R hR
  refine ⟨⋃ i, ((R i : Γ₁)⁻¹) • 𝓕, ?_, ?_⟩
  ·
    refine isFundamentalDomain_of_bijective hfd
      (fun g : Γ₂' => (⟨((g : Γ₁) : G), g.2⟩ : Γ₂)) ⟨?_, ?_⟩ (fun _ _ => rfl)
    · intro a b hab
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun g : Γ₂ => (g : G)) hab
    · intro g
      exact ⟨⟨⟨g.1, hle g.2⟩, g.2⟩, rfl⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨(R i : Γ₁)⁻¹, hi⟩

section Slab

open NumberField NumberField.AdelicHaar

variable (F : Type) [Field F] [NumberField F]

def slab (α β : ℝ) : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem ideleNorm_det_globalPoints (γ : GL (Fin 2) F) :
    NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 F) F γ)) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  unfold NumberField.TateGlobal.ideleNorm AutomorphicForm.globalPoints
  rw [Matrix.GeneralLinearGroup.map_det]
  have := NumberField.AdeleRing.distribHaarChar_algebraMap F (Matrix.GeneralLinearGroup.det γ)
  simp only [RingHom.toMonoidHom_eq_coe] at this
  rw [this]
  simp

theorem globalPoints_mul_mem_slab_iff (α β : ℝ) (γ : GL (Fin 2) F)
    (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    AutomorphicForm.globalPoints (𝓞 F) F γ * g ∈ slab F α β ↔ g ∈ slab F α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    ideleNorm_det_globalPoints, one_mul]

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem borelSpace_adelicGL2 : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
  NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F

attribute [local instance] borelSpace_adelicGL2

theorem smulInvariantMeasure_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (AutomorphicForm.globalPoints (𝓞 F) F).range
      (AutomorphicForm.AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β)) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨_, γ, rfl⟩ := γ
  have hmeas : MeasurableSet ((fun x : AutomorphicForm.AdelicGL2 (𝓞 F) F =>
      AutomorphicForm.globalPoints (𝓞 F) F γ * x) ⁻¹' s) := (measurable_const_mul _) hs
  change ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β))
      ((fun x => AutomorphicForm.globalPoints (𝓞 F) F γ * x) ⁻¹' s) = _
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => AutomorphicForm.globalPoints (𝓞 F) F γ * x) ⁻¹' s ∩ slab F α β =
      (fun x => AutomorphicForm.globalPoints (𝓞 F) F γ * x) ⁻¹' (s ∩ slab F α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [hset, measure_preimage_mul]

theorem countable_GL2 : Countable (GL (Fin 2) F) := by
  haveI : Countable F := (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) F → _)) Units.val_injective

scoped instance countable_range_globalPoints : Countable (AutomorphicForm.globalPoints (𝓞 F) F).range := by
  haveI := countable_GL2 F
  exact Set.countable_range _ |>.to_subtype

theorem exists_isFundamentalDomain_of_le_range (α β : ℝ) (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hΦs : Φ ⊆ slab F α β)
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β)))
    (Γ : Subgroup (GL (Fin 2) F)) :
    ∃ Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F),
      IsFundamentalDomain (Γ.map (AutomorphicForm.globalPoints (𝓞 F) F)) Ψ
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β)) ∧ Ψ ⊆ slab F α β := by
  haveI := smulInvariantMeasure_restrict_slab F α β
  obtain ⟨Ψ, hΨ, hsub⟩ := exists_isFundamentalDomain_subgroup
    ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β))
    (AutomorphicForm.globalPoints (𝓞 F) F).range (Γ.map (AutomorphicForm.globalPoints (𝓞 F) F))
    (Subgroup.map_le_range _ _) Φ hΦ
  refine ⟨Ψ, hΨ, hsub.trans ?_⟩
  intro x hx
  obtain ⟨γ, hγ⟩ := Set.mem_iUnion.1 hx
  obtain ⟨_, g, rfl⟩ := γ
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hγ
  exact (globalPoints_mul_mem_slab_iff F α β g y).2 (hΦs hy)

end Slab

section Ideles

open NumberField

theorem exists_isFundamentalDomain_ideles (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (Γ : Subgroup (AdeleRing (𝓞 F) F)ˣ)
    (hΓ : Γ ≤ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range) :
    ∃ Θ : Set (AdeleRing (𝓞 F) F)ˣ, IsFundamentalDomain Γ Θ ν := by
  haveI : Countable F := (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable Fˣ := Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective
  haveI : Countable (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range :=
    Set.countable_range _ |>.to_subtype
  obtain ⟨Θ, hΘ, -⟩ := exists_isFundamentalDomain_subgroup ν _ Γ hΓ Ω hΩ
  exact ⟨Θ, hΘ⟩

end Ideles

section TwistedScalarConj

variable {G U : Type*} [Group G] [Group U] (s : U →* G) (σ' : G →* G)
  (hcen : ∀ (u : U) (g : G), Commute (s u) g)

def TSRel (x y : G) : Prop := ∃ (h : G) (u : U), x = s u * (h⁻¹ * y * σ' h)

include hcen

omit hcen in
theorem tsRel_refl (x : G) : TSRel s σ' x x := ⟨1, 1, by simp⟩

theorem tsRel_symm {x y : G} (hxy : TSRel s σ' x y) : TSRel s σ' y x := by
  obtain ⟨h, u, rfl⟩ := hxy
  refine ⟨h⁻¹, u⁻¹, ?_⟩
  have h1 : (h⁻¹)⁻¹ * (s u * (h⁻¹ * y * σ' h)) * σ' h⁻¹ = s u * ((h⁻¹)⁻¹ * (h⁻¹ * y * σ' h) * σ' h⁻¹) := by
    rw [← mul_assoc (h⁻¹)⁻¹ (s u), ((hcen u (h⁻¹)⁻¹).symm).eq]
    simp only [mul_assoc]
  rw [h1, map_inv, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]
  group

theorem tsRel_trans {x y z : G} (hxy : TSRel s σ' x y) (hyz : TSRel s σ' y z) : TSRel s σ' x z := by
  obtain ⟨h, u, rfl⟩ := hxy
  obtain ⟨k, v, rfl⟩ := hyz
  refine ⟨k * h, u * v, ?_⟩
  have h1 : h⁻¹ * (s v * (k⁻¹ * z * σ' k)) * σ' h = s v * (h⁻¹ * (k⁻¹ * z * σ' k) * σ' h) := by
    rw [← mul_assoc h⁻¹ (s v), ((hcen v h⁻¹).symm).eq]
    simp only [mul_assoc]
  rw [h1, map_mul, map_mul, mul_inv_rev]
  simp only [mul_assoc]

end TwistedScalarConj

theorem commute_scalar {F : Type*} [CommRing F] (u : Fˣ) (g : GL (Fin 2) F) :
    Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) u) g := by
  rw [Commute, SemiconjBy]
  apply Units.ext
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (u : F) (fun r' => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) F)).eq

end R2FafR
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_twistedEllipticCentralFold_eq_const_mul_sum_of_factorization_of_normFibre.R2FafR"

section
open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel

p2m_open "AutomorphicForm~ideleNorm_det_globalPoints" in
theorem m852_explicit
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
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
    (hLG : ∀ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K →
      (∀ v : HeightOneSpectrum (𝓞 K), ∃ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ.symm
          (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) γ) δv) →
      (∃ δa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
        AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ.symm
          (Matrix.GeneralLinearGroup.map (algebraMap K (InfiniteAdeleRing K)) γ) δa) →
      LT.TwistedNorm.IsNormClass hgen (ConjClasses.mk γ))
    (hEuler : ∀ (μL : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
        (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))),
      @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
        (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μL →
      ∃ c₀ : NNReal, c₀ ≠ 0 ∧
        ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
        ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ),
          AutomorphicForm.AreMatchingAt K L σ.symm S' φ f →
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
            (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
              Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
            AutomorphicForm.AreMatchingLocal K L v σ.symm
              ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
              ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) →
          AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ.symm μL
            (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
            (φ ∘ Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
            f)
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (cK cL : ℝ) (hcK : 0 < cK) (hcL : 0 < cL)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa (AutomorphicForm.archHaarK K) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v) (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈ AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉ AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = cK * (∫ x, fa x ∂(AutomorphicForm.archHaarK K)) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (hG' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (F : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (FS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] Fa (AutomorphicForm.archHaarL K L) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (FS v) (AutomorphicForm.semiLocalHaar K L v)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = Fa (AutomorphicForm.tensorArch K L x) * ∏ v ∈ S, FS v (AutomorphicForm.tensorPlace K L v x)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) → F x = 0) →
          ∫ x, F x ∂(@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) (Matrix.GeneralLinearGroup.map (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom)) (adelicGLHaar (Fin 2) (𝓞 L) L)) = cL * (∫ y, Fa y ∂(AutomorphicForm.archHaarL K L)) * ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))
    (c₀ : NNReal) (hc₀ : (c₀ : ℝ) * cK = cL)
    (κ : ℝ) (hκ : 0 < κ)
    (hκl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        ENNReal.ofReal κ *
          ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hκi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
      (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
        IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
      ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        κ * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK) :
    ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
    ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ)
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
      (_hm : AutomorphicForm.AreMatchingAt K L σ.symm S' φ f)
      (_hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
        (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
          Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
        AutomorphicForm.AreMatchingLocal K L v σ.symm
          ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))),
      (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
              (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
              LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (((c₀ : ℝ) * κ / ((Module.finrank K L : ℝ) * ((max 1 Ξ.card : ℕ) : ℝ)) : ℝ) : ℂ) * ∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  classical

  obtain ⟨RL, hRLsub, hRL⟩ := R2FafR.exists_representatives
    {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ}
    (fun δ δ₀ => R2FafR.TSRel (Matrix.GeneralLinearGroup.scalar (Fin 2))
      (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ δ₀)
    (R2FafR.tsRel_refl _ _)
    (fun _ _ h => R2FafR.tsRel_symm _ _ R2FafR.commute_scalar h)
    (fun _ _ _ h₁ h₂ => R2FafR.tsRel_trans _ _ R2FafR.commute_scalar h₁ h₂)
  obtain ⟨RK, hRKsub, hRK⟩ := R2FafR.exists_representatives
    (AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K)
    (fun γ γ₀ => R2FafR.TSRel (Matrix.GeneralLinearGroup.scalar (Fin 2)) (MonoidHom.id _) γ γ₀)
    (R2FafR.tsRel_refl _ _)
    (fun _ _ h => R2FafR.tsRel_symm _ _ R2FafR.commute_scalar h)
    (fun _ _ _ h₁ h₂ => R2FafR.tsRel_trans _ _ R2FafR.commute_scalar h₁ h₂)

  have hΨL' := fun δ₀ : GL (Fin 2) L => R2FafR.exists_isFundamentalDomain_of_le_range L α β ΦL hΦs hΦ
    (AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀)
  choose ΨL hΨL hΨLs using hΨL'
  have hΨK' := fun γ₀ : GL (Fin 2) K => R2FafR.exists_isFundamentalDomain_of_le_range K α β ΦK hΦKs hΦK
    (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K)))
  choose ΨK hΨK hΨKs using hΨK'

  have hCU :=
    d10_explicit
      K L hprime α β hα hαβ νZL D σ hσ hgen SK hS ξL hξc hξt Ξ hΞ νZK RL hRLsub hRL ΨL
      (fun δ₀ _ => hΨLs δ₀) (fun δ₀ _ => hΨL δ₀) Θ hΘ RK hRKsub hRK ΨK (fun γ₀ _ => hΨKs γ₀)
      (fun γ₀ _ => hΨK γ₀) hLG hEuler
      cK cL hcK hcL hG hG' c₀ hc₀ κ hκ hκl hκi
  intro S' hS' φ hφ hφc f hf hfc hm hunit

  have hL :=
    AutomorphicForm.setIntegral_twistedCentralEllipticFold_eq_finsum_inv_card_mul_setIntegral_sigmaCentralizerDomain
      K L σ.symm hgen α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D ξL hξc hξt φ hφ hφc RL hRLsub hRL ΨL
      (fun δ₀ _ => hΨLs δ₀) (fun δ₀ _ => hΨL δ₀) Θ hΘ

  have hK : ∀ ξK ∈ Ξ,
      (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      ∑ᶠ γ₀ ∈ RK,
        ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
            Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
          ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK :=
    fun ξK hξK =>
      AutomorphicForm.setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain
        K α β hα hαβ ΦK hΦKs hΦK νZK ΩK hΩK ξK ((hΞ ξK).1 hξK).1 ((hΞ ξK).1 hξK).2.1 f hf hfc RK hRKsub
        hRK ΨK (fun γ₀ _ => hΨKs γ₀) (fun γ₀ _ => hΨK γ₀)
  rw [hL, Finset.sum_congr rfl hK]
  exact hCU S' hS' φ hφ hφc f hf hfc hm hunit

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_twistedEllipticCentralFold_eq_const_mul_sum_of_factorization_of_normFibre.R2FafR"

section CM1TopSection
open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

p2m_open "AutomorphicForm~ideleNorm_det_globalPoints" in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
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
    (N : Ideal (𝓞 L)) (tysL : AutomorphicForm.ArchTypeFamily L)
    (N' : Ideal (𝓞 K)) (tysK : AutomorphicForm.ArchTypeFamily K)
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

    (cK cL : ℝ) (hcK : 0 < cK) (hcL : 0 < cL)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa (AutomorphicForm.archHaarK K) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v) (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈ AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉ AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = cK * (∫ x, fa x ∂(AutomorphicForm.archHaarK K)) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (hG' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (F : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (FS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] Fa (AutomorphicForm.archHaarL K L) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (FS v) (AutomorphicForm.semiLocalHaar K L v)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = Fa (AutomorphicForm.tensorArch K L x) * ∏ v ∈ S, FS v (AutomorphicForm.tensorPlace K L v x)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) → F x = 0) →
          ∫ x, F x ∂(@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) (Matrix.GeneralLinearGroup.map (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom)) (adelicGLHaar (Fin 2) (𝓞 L) L)) = cL * (∫ y, Fa y ∂(AutomorphicForm.archHaarL K L)) * ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))

    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (hμAK : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
        ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νZK)
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ.symm q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))

    (C : ℝ) (hC : 0 < C)
    (hCl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ENNReal, Measurable g →
        ∫⁻ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          ENNReal.ofReal C *
            ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hCi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
        (Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)))
            (HaarQuotient.measure νZL N1 μN) ↔
          IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          C * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK) :
    ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
    ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ)
      (_hφt : AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
        (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ)
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
      (_hft : AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
        (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f)
      (_hm : AutomorphicForm.AreMatchingAt K L σ.symm S' φ f)
      (_hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
        (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
          Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
        AutomorphicForm.AreMatchingLocal K L v σ.symm
          ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))),
      (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
              (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
              LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (((cL / cK) * cN * C * (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal / (νZK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal / ((max 1 Ξ.card : ℕ) : ℝ) : ℝ) : ℂ) * ∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  classical

  obtain ⟨Θ, hΘ⟩ := R2FafR.exists_isFundamentalDomain_ideles L νZL ΩL hΩL
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
      (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range
    (by rw [MonoidHom.range_comp]; exact Subgroup.map_le_range _ _)

  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := CM1Top.secondCountableTopology_units _
  haveI : SecondCountableTopology N1 := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨V₀, hV₀o, hV₀⟩ := NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton L
  have hΓle : ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range ≤
      M4aHerbrand.principalIdeles (𝓞 L) L := by
    rw [MonoidHom.range_comp]; exact Subgroup.map_le_range _ _
  obtain ⟨Θ₁, hΘ₁B, hΘ₁ex⟩ := Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology
      ((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1)
      ⟨Subtype.val ⁻¹' V₀, hV₀o.preimage continuous_subtype_val, by
        ext n
        simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨hnV, hnΓ⟩
          have hmem : (n : (AdeleRing (𝓞 L) L)ˣ) ∈ V₀ ∩ (M4aHerbrand.principalIdeles (𝓞 L) L : Set _) :=
            ⟨hnV, hΓle hnΓ⟩
          rw [hV₀, Set.mem_singleton_iff] at hmem
          exact Subtype.ext (by simpa using hmem)
        · rintro rfl
          have h1 : (1 : (AdeleRing (𝓞 L) L)ˣ) ∈ V₀ ∩ (M4aHerbrand.principalIdeles (𝓞 L) L : Set _) := by
            rw [hV₀]; exact Set.mem_singleton _
          exact ⟨h1.1, Subgroup.one_mem _⟩⟩
  have hΘ₁ : IsFundamentalDomain ((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1) Θ₁ μN := by
    refine IsFundamentalDomain.mk' ?_ ?_
    · obtain ⟨U, Cc, hU, hCc, rfl⟩ := hΘ₁B
      exact (MeasurableSet.iUnion fun n => ((hU n).measurableSet.diff (hCc n).measurableSet)).nullMeasurableSet
    · intro x
      simpa only [Subgroup.smul_def, smul_eq_mul] using hΘ₁ex x

  have hμNΘ₁ :=
    NumberField.measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm
      K L D σ.symm hgen νZL ΩL hΩL νZK ΩK hΩK AK hAKc hAK μAK hμAK N1 hN1c hN1 μN cN hcN hNc Θ₁ hΘ₁
  obtain ⟨VL, hVLpos, hVL, -⟩ :=
    NumberField.AdelicHeight.exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
      L L νZL ΩL hΩL (MonoidHom.id _) continuous_id 1 one_pos (fun y => by simp)
  obtain ⟨VK, hVKpos, hVK, -⟩ :=
    NumberField.AdelicHeight.exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
      K K νZK ΩK hΩK (MonoidHom.id _) continuous_id 1 one_pos (fun y => by simp)
  have he : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hVLeq : (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal = VL := by
    have h := hVL 1 (Real.exp 1) one_pos he
    rw [Real.log_exp, Real.log_one, sub_zero, mul_one, measureReal_def] at h
    exact h
  have hVKeq : (νZK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal = VK := by
    have h := hVK 1 (Real.exp 1) one_pos he
    rw [Real.log_exp, Real.log_one, sub_zero, mul_one, measureReal_def] at h
    exact h
  have hℓ : 0 < (Module.finrank K L : ℝ) := by exact_mod_cast hprime.pos
  have hr0 : 0 < cN * (Module.finrank K L : ℝ) * VL / VK := by positivity
  have hμN' : μN Θ₁ = ENNReal.ofReal (cN * (Module.finrank K L : ℝ) * VL / VK) := by
    rw [hμNΘ₁, hVLeq, hVKeq]
  have hSt :=
    NumberField.setLIntegral_comp_idelicNorm_fundamentalDomain_eq_measure_mul_lintegral_haarQuotient_ker
      K L σ.symm νZL N1 hN1c hN1 μN Θ hΘ Θ₁ hΘ₁
  have hκ : 0 < cN * (Module.finrank K L : ℝ) * VL / VK * C := mul_pos hr0 hC
  have hκl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        ENNReal.ofReal (cN * (Module.finrank K L : ℝ) * VL / VK * C) *
          ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK := by
    intro g hg
    rw [hSt.1 g hg, hCl g hg, hμN', ← mul_assoc, ← ENNReal.ofReal_mul hr0.le]
  have hκi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
      (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
        IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
      ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        (cN * (Module.finrank K L : ℝ) * VL / VK * C : ℝ) *
          ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK := by
    intro g hg
    have hfin : μN Θ₁ < ∞ := by rw [hμN']; exact ENNReal.ofReal_lt_top
    obtain ⟨h1, h2⟩ := hSt.2 hfin g hg
    obtain ⟨h3, h4⟩ := hCi g hg
    have hne : μN Θ₁ ≠ 0 := by rw [hμN']; exact (ENNReal.ofReal_pos.2 hr0).ne'
    refine ⟨?_, ?_⟩
    · rw [h1, or_iff_right hne, h3]
    · rw [h2, h4, hμN', ENNReal.toReal_ofReal hr0.le]
      push_cast
      ring

  let c₀ : NNReal := ⟨cL / cK, (div_pos hcL hcK).le⟩
  have hc₀ : (c₀ : ℝ) * cK = cL := by
    show cL / cK * cK = cL
    field_simp

  have H := m852_explicit K L hprime α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hσ hgen SK hS ξL hξc hξt Ξ hΞ
      ΦK hΦKs hΦK νZK ΩK hΩK
      (fun γ hγ hfin harch =>
        AutomorphicForm.isNormClass_mk_of_mem_ellipticCell_of_forall_isNormOf K L hgen γ hγ hfin harch)
      (fun μL hμL =>
        AutomorphicForm.exists_areMatchingOn_adeleRing_of_areMatchingAt_of_prime K L hprime σ.symm
          (fun h => hσ (by first | simpa using congrArg AlgEquiv.symm h | (have h_1 := congrArg AlgEquiv.symm h; simp at h_1; exact h_1) | (have h_1 := congrArg AlgEquiv.symm h; simp at h_1 ⊢; exact h_1) | exact (congrArg AlgEquiv.symm h))) SK hS μL hμL)
      Θ hΘ cK cL hcK hcL hG hG' c₀ hc₀ _ hκ hκl hκi
  intro S' hS' φ hφ hφc _ f hf hfc _ hm hunit
  rw [H S' hS' φ hφ hφc f hf hfc hm hunit, hVLeq, hVKeq]
  congr 1
  have hcK0 : cK ≠ 0 := hcK.ne'
  have hVK0 : VK ≠ 0 := hVKpos.ne'
  have hℓ0 : (Module.finrank K L : ℝ) ≠ 0 := hℓ.ne'
  have hM0 : ((max 1 Ξ.card : ℕ) : ℝ) ≠ 0 := by positivity
  have hc₀v : ((c₀ : ℝ)) = cL / cK := rfl
  have key : (c₀ : ℝ) * (cN * (Module.finrank K L : ℝ) * VL / VK * C) /
        ((Module.finrank K L : ℝ) * ((max 1 Ξ.card : ℕ) : ℝ)) =
      (cL / cK) * cN * C * VL / VK / ((max 1 Ξ.card : ℕ) : ℝ) := by
    rw [hc₀v]
    field_simp
  rw [key]

end CM1TopSection
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_twistedEllipticCentralFold_eq_const_mul_sum_of_factorization_of_normFibre.R2FafR"

end S_AutomorphicForm_setIntegral_twistedEllipticCentralFold_eq_const_mul_sum_of_factorization_of_normFibre
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_twistedEllipticCentralFold_eq_const_mul_sum_of_factorization_of_normFibre (solution)
