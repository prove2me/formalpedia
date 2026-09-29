-- Prove2me | solution 1 for AutomorphicForm.exists_finsum_sigmaCentralizerDomain_eq_mul_sum_finsum_centralizerDomain_of_areMatchingOn_of_isNormClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/eabba619-b6a3-5306-bb54-f1a2fe6e4f1a

import Theorems.Thm_AutomorphicForm_exists_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime
import Theorems.Thm_AutomorphicForm_finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_areMatchingOn_of_eq_zero
import Theorems.Thm_AutomorphicForm_finsum_sigmaCentralizerDomain_centralNorm_eq_mul_sum_finsum_centralizerDomain_central_of_central_transfer
import Theorems.Thm_NumberField_exists_setLIntegral_comp_idelicNorm_eq_mul_and_setIntegral_comp_idelicNorm_eq_mul
import Theorems.Thm_AutomorphicForm_isNormOf_map_of_isNormOf
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finsum_sigmaCentralizerDomain_eq_mul_sum_finsum_centralizerDomain_of_areMatchingOn_of_isNormClass
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups"
p2m_attr_erase "instance" "ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk"
p2m_attr_erase "simp" "Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe"
p2m_attr_erase "simp" "LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk groupCohomology.Cores.Transversal.mk.sizeOf_spec"
p2m_attr_erase "simp" "groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.cpowChar_apply_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.gl2Weyl_val"

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

theorem solution
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
            f) :
  ∃ c : ℂ, c ≠ 0 ∧
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
      c * ∑ ξK ∈ Ξ, ∑ᶠ γ₀ ∈ RK,
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
  obtain ⟨c₀, hc₀, hboth⟩ :=
    AutomorphicForm.exists_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime
      K L hprime σ.symm hσ' SK hS _ hHaar

  obtain ⟨κ, hκ, hκl, hκi⟩ :=
    NumberField.exists_setLIntegral_comp_idelicNorm_eq_mul_and_setIntegral_comp_idelicNorm_eq_mul
      K L σ.symm hgen νZL νZK Θ hΘ

  have hℓ : 0 < (Module.finrank K L : ℝ) := by exact_mod_cast hprime.pos
  have hmax : 0 < ((max 1 Ξ.card : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (le_max_left 1 Ξ.card))
  have hc₀' : 0 < (c₀ : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hc₀)
  refine ⟨(((c₀ : ℝ) * κ / ((Module.finrank K L : ℝ) * ((max 1 Ξ.card : ℕ) : ℝ)) : ℝ) : ℂ), ?_, ?_⟩
  · exact_mod_cast (div_pos (mul_pos hc₀' hκ) (mul_pos hℓ hmax)).ne'
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

end S_AutomorphicForm_exists_finsum_sigmaCentralizerDomain_eq_mul_sum_finsum_centralizerDomain_of_areMatchingOn_of_isNormClass
end P2MW
export P2MW.S_AutomorphicForm_exists_finsum_sigmaCentralizerDomain_eq_mul_sum_finsum_centralizerDomain_of_areMatchingOn_of_isNormClass (solution)
