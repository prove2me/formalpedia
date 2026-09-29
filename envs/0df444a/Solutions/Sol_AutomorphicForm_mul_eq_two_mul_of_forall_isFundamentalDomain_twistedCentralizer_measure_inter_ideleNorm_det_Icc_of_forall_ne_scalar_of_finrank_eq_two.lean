-- Prove2me | solution 1 for AutomorphicForm.mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e7cadc72-e523-5044-887f-fbf2c9519fa4

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_globalPoints_inter_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "AutomorphicForm.cpowChar_apply_val AutomorphicForm.whittakerCoefficient_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply ContinuousAddEquiv.preimage_mulLeft_smul NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply"
p2m_attr_erase "simp" "NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicHaar NumberField.AdelicLevel TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "tensorArch tensorPlace isTopologicalRing_tensor isTopologicalGroup_tensorGL glBorelOf centralizerBorel toTensorGL semiLocalIntegralSet sigmaTensor normString IsSigmaConjugate IsNormConjugator twistedCentralizer twistedCentralizerBorel localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localHaar_localIntegralSet AdelicGL2 globalPoints centralScalar sigmaCentralizer rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_globalPoints_inter_ideleNorm_det_Icc two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two"
namespace MassReduction
p2m_open "AutomorphicForm"

section LinearAlgebra

variable {R : Type*} [CommRing R]

abbrev sc (c : Rˣ) : GL (Fin 2) R := Matrix.GeneralLinearGroup.scalar (Fin 2) c

theorem scalar_mul_comm (c : Rˣ) (g : GL (Fin 2) R) : sc c * g = g * sc c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (g : Matrix (Fin 2) (Fin 2) R) =
    (g : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

theorem centralizer_scalar_eq_top (c : Rˣ) :
    Subgroup.centralizer ({sc c} : Set (GL (Fin 2) R)) = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff, SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  exact (scalar_mul_comm c g).symm

end LinearAlgebra

section Places

abbrev Gad (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (AdeleRing (𝓞 K) K)

abbrev Garch (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (InfiniteAdeleRing K)

abbrev Gv (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : Type := GL (Fin 2) (v.adicCompletion K)

abbrev Gsl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  GL (Fin 2) (L ⊗[K] v.adicCompletion K)

section Instances

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

scoped instance instSecondCountableCompletion (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance instSecondCountableInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) :=
  show SecondCountableTopology ((w : InfinitePlace K) → w.Completion) from inferInstance

scoped instance instSecondCountableMulOpposite (X : Type*) [TopologicalSpace X] [Mul X]
    [SecondCountableTopology X] : SecondCountableTopology Xᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountable_gl (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [SecondCountableTopology A] : SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance instSecondCountableGarch : SecondCountableTopology (Garch K) := secondCountable_gl _
scoped instance instSecondCountableGv (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (Gv K v) :=
  secondCountable_gl _

scoped instance instLocallyCompactGarch : LocallyCompactSpace (Garch K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
scoped instance instLocallyCompactGv (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gv K v) :=
  locallyCompactSpace_localGL K v
scoped instance instT2Garch : T2Space (Garch K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  exact Units.isEmbedding_embedProduct.t2Space
scoped instance instT2Gv (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gv K v) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → v.adicCompletion K))
  exact Units.isEmbedding_embedProduct.t2Space
scoped instance instT2Gad : T2Space (Gad K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  exact Units.isEmbedding_embedProduct.t2Space

scoped instance instIsTopologicalRingSL (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalRing (L ⊗[K] v.adicCompletion K) :=
  isTopologicalRing_tensor K L _
scoped instance instIsTopologicalGroupGsl (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalGroup (Gsl K L v) :=
  isTopologicalGroup_tensorGL K L _

scoped instance instMeasurableSpaceGarch : MeasurableSpace (Garch K) := borel _
scoped instance instBorelSpaceGarch : BorelSpace (Garch K) := ⟨rfl⟩
scoped instance instMeasurableSpaceGv (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gv K v) := borel _
scoped instance instBorelSpaceGv (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gv K v) := ⟨rfl⟩
scoped instance instMeasurableSpaceGad : MeasurableSpace (Gad K) := borel _
scoped instance instBorelSpaceGad : BorelSpace (Gad K) := ⟨rfl⟩
scoped instance instMeasurableSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gsl K L v) := borel _
scoped instance instBorelSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gsl K L v) := ⟨rfl⟩

scoped instance (priority := 10000) instMeasurableSpaceSubgroupGad (H : Subgroup (Gad K)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupGad (H : Subgroup (Gad K)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGsl (v : HeightOneSpectrum (𝓞 K))
    (H : Subgroup (Gsl K L v)) : MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGsl (v : HeightOneSpectrum (𝓞 K)) (H : Subgroup (Gsl K L v)) :
    BorelSpace H := ⟨rfl⟩

scoped instance instIsHaarLocalHaar (v : HeightOneSpectrum (𝓞 K)) : IsHaarMeasure (localHaar K v) := isHaarMeasure_localHaar K v

scoped instance instLocallyCompactCentralizerGad (u : (AdeleRing (𝓞 K) K)ˣ) :
    LocallyCompactSpace (Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K))) := by
  have h : IsClosed ((Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)) : Set (Gad K))) := by
    rw [show centralScalar (𝓞 K) K u = sc u from rfl, centralizer_scalar_eq_top]
    exact isClosed_univ
  exact h.locallyCompactSpace

end Instances

end Places

section Transport

variable {K : Type} [Field K] [NumberField K]

def centralizerCsEquiv (u : (AdeleRing (𝓞 K) K)ˣ) :
    Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)) ≃ₜ* Gad K :=
  { (MulEquiv.subgroupCongr (centralizer_scalar_eq_top (R := AdeleRing (𝓞 K) K) u)).trans Subgroup.topEquiv with
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk continuous_id }

theorem centralizerCsEquiv_apply (u : (AdeleRing (𝓞 K) K)ˣ)
    (t : Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K))) :
    centralizerCsEquiv u t = (t : Gad K) := rfl

theorem mem_centralizer_centralScalar (u : (AdeleRing (𝓞 K) K)ˣ) (g : Gad K) :
    g ∈ Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)) := by
  rw [show centralScalar (𝓞 K) K u = sc u from rfl, centralizer_scalar_eq_top]; trivial

def centralizerCsMeasEquiv (u : (AdeleRing (𝓞 K) K)ˣ) :
    Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)) ≃ᵐ Gad K :=
  (centralizerCsEquiv u).toHomeomorph.toMeasurableEquiv

theorem centralizerCsMeasEquiv_apply (u : (AdeleRing (𝓞 K) K)ˣ)
    (t : Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K))) :
    centralizerCsMeasEquiv u t = (t : Gad K) := rfl

theorem coe_centralizerCsMeasEquiv (u : (AdeleRing (𝓞 K) K)ˣ) :
    (centralizerCsMeasEquiv u : _ → Gad K) = centralizerCsEquiv u := rfl

def band (K : Type) [Field K] [NumberField K] (a b : ℝ) : Set (Gad K) :=
  {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

variable (u : (AdeleRing (𝓞 K) K)ˣ)
  (τ : Measure (Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)))) [τ.IsHaarMeasure]

def τG : Measure (Gad K) := Measure.map (centralizerCsEquiv u) τ

scoped instance isHaarMeasure_τG : (τG u τ).IsHaarMeasure :=
  ContinuousMulEquiv.isHaarMeasure_map τ (centralizerCsEquiv u)

theorem τG_eq_map : τG u τ = Measure.map (centralizerCsMeasEquiv u) τ := rfl

theorem integral_τG (W : Gad K → ℂ) : ∫ g, W g ∂(τG u τ) = ∫ t, W (t : Gad K) ∂τ := by
  rw [τG_eq_map, integral_map_equiv]
  rfl

theorem τG_apply (A : Set (Gad K)) : τG u τ A = τ (Subtype.val ⁻¹' A) := by
  rw [τG_eq_map, MeasurableEquiv.map_apply]
  rfl

theorem isFundamentalDomain_preimage {D : Set (Gad K)}
    (hFD : IsFundamentalDomain ((globalPoints (𝓞 K) K).range).op D (τG u τ)) :
    IsFundamentalDomain
      (((globalPoints (𝓞 K) K).range).subgroupOf
        (Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)))).op
      ((Subtype.val : Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)) → Gad K) ⁻¹' D) τ := by
  classical
  let H : Subgroup (Gad K) := Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K))
  let Γ : Subgroup (Gad K) := (globalPoints (𝓞 K) K).range

  let toH : Gad K → H := fun g => ⟨g, mem_centralizer_centralScalar u g⟩
  have toH_mem : ∀ γ : Γ.op, MulOpposite.op (toH (MulOpposite.unop (γ : (Gad K)ᵐᵒᵖ))) ∈ (Γ.subgroupOf H).op := by
    intro γ
    rw [Subgroup.mem_op, MulOpposite.unop_op, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_op.mp γ.2
  let e : Γ.op → (Γ.subgroupOf H).op := fun γ =>
    ⟨MulOpposite.op (toH (MulOpposite.unop (γ : (Gad K)ᵐᵒᵖ))), toH_mem γ⟩
  have he : Function.Bijective e := by
    constructor
    · intro γ₁ γ₂ h
      have h1 : ((MulOpposite.unop ((e γ₁ : (Γ.subgroupOf H).op) : Hᵐᵒᵖ) : H) : Gad K) =
          ((MulOpposite.unop ((e γ₂ : (Γ.subgroupOf H).op) : Hᵐᵒᵖ) : H) : Gad K) := by rw [h]
      exact Subtype.ext (MulOpposite.unop_injective h1)
    · intro δ
      refine ⟨⟨MulOpposite.op ((MulOpposite.unop (δ : Hᵐᵒᵖ) : H) : Gad K), ?_⟩, ?_⟩
      · rw [Subgroup.mem_op, MulOpposite.unop_op]
        have := δ.2
        rw [Subgroup.mem_op, Subgroup.mem_subgroupOf] at this
        exact this
      · rfl
  have hqmp : Measure.QuasiMeasurePreserving (Subtype.val : H → Gad K) τ (τG u τ) := by
    have hmp : MeasurePreserving (centralizerCsMeasEquiv u) τ (τG u τ) :=
      ⟨(centralizerCsMeasEquiv u).measurable, rfl⟩
    exact hmp.quasiMeasurePreserving
  refine hFD.preimage_of_equiv hqmp he fun γ => ?_
  intro x
  rfl

end Transport

section Local

variable {K : Type} [Field K] [NumberField K]

theorem measurableSet_localIntegralSet (v : HeightOneSpectrum (𝓞 K)) : MeasurableSet (localIntegralSet K v) :=
  (isOpen_localIntegralSet K v).measurableSet

theorem localIntegralSet_pos (v : HeightOneSpectrum (𝓞 K)) (μ : Measure (Gv K v)) [μ.IsHaarMeasure] :
    0 < μ (localIntegralSet K v) :=
  (isOpen_localIntegralSet K v).measure_pos μ ⟨1, one_mem_localIntegralSet K v⟩

theorem localIntegralSet_lt_top (v : HeightOneSpectrum (𝓞 K)) (μ : Measure (Gv K v)) [μ.IsHaarMeasure] :
    μ (localIntegralSet K v) < ⊤ :=
  (isCompact_localIntegralSet K v).measure_lt_top

theorem eq_smul_localHaar (v : HeightOneSpectrum (𝓞 K)) (μ : Measure (Gv K v)) [μ.IsHaarMeasure] :
    μ = μ (localIntegralSet K v) • localHaar K v := by
  have h := isMulLeftInvariant_eq_smul μ (localHaar K v)
  have hc : μ (localIntegralSet K v) = haarScalarFactor μ (localHaar K v) := by
    conv_lhs => rw [h]
    rw [Measure.coe_nnreal_smul_apply, localHaar_localIntegralSet, mul_one]
  rw [hc]
  exact h

theorem integral_indicator_one_complex {X : Type*} [MeasurableSpace X] (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) : ∫ x, A.indicator (fun _ => (1 : ℂ)) x ∂μ = ((μ.real A : ℝ) : ℂ) := by
  rw [integral_indicator_const (1 : ℂ) hA, Complex.real_smul, mul_one]

theorem localMass_eq_one_of_prod (τa : Measure (Garch K)) [τa.IsHaarMeasure]
    (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Gv K v)) [∀ v, (τf v).IsHaarMeasure]
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (τ : Measure (Gad K)) (cτ : ℝ) (hcτ : 0 < cτ)
    (hτprod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : Gad K → ℂ) (Wa : Garch K → ℂ) (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gv K v → ℂ),
        AEStronglyMeasurable Wa τa → (∀ v ∈ S, AEStronglyMeasurable (WS v) (τf v)) →
        (∀ t : Gad K, (∀ v ∉ S, finComponent (𝓞 K) K v (glFin (𝓞 K) K t) ∈ localIntegralSet K v) →
            W t = Wa (glArch (𝓞 K) K t) * ∏ v ∈ S, WS v (finComponent (𝓞 K) K v (glFin (𝓞 K) K t))) →
        (∀ t : Gad K, (∃ v ∉ S, finComponent (𝓞 K) K v (glFin (𝓞 K) K t) ∉ localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cτ * (∫ x, Wa x ∂τa) * ∏ v ∈ S, ∫ y, WS v y ∂(τf v))
    (v₀ : HeightOneSpectrum (𝓞 K)) (hv₀ : v₀ ∉ S₀) :
    τf v₀ (localIntegralSet K v₀) = 1 := by
  classical

  obtain ⟨Ca, hCa, hCa1⟩ := exists_compact_mem_nhds (1 : Garch K)
  have hCam : MeasurableSet Ca := hCa.isClosed.measurableSet
  have hCapos : 0 < τa Ca := measure_pos_of_mem_nhds τa hCa1
  have hCatop : τa Ca < ⊤ := hCa.measure_lt_top

  let Box : Set (Gad K) := {t | glArch (𝓞 K) K t ∈ Ca ∧
    ∀ w : HeightOneSpectrum (𝓞 K), finComponent (𝓞 K) K w (glFin (𝓞 K) K t) ∈ localIntegralSet K w}
  let W : Gad K → ℂ := Box.indicator fun _ => (1 : ℂ)
  let Wa : Garch K → ℂ := Ca.indicator fun _ => (1 : ℂ)
  let WS : ∀ w : HeightOneSpectrum (𝓞 K), Gv K w → ℂ := fun w => (localIntegralSet K w).indicator fun _ => (1 : ℂ)
  have hWa : AEStronglyMeasurable Wa τa := aestronglyMeasurable_const.indicator hCam
  have hWS : ∀ w, AEStronglyMeasurable (WS w) (τf w) := fun w =>
    aestronglyMeasurable_const.indicator (measurableSet_localIntegralSet w)

  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S →
      ∫ t, W t ∂τ = cτ * (∫ x, Wa x ∂τa) * ∏ v ∈ S, ∫ y, WS v y ∂(τf v) := by
    intro S hS
    refine hτprod S hS W Wa WS hWa (fun w _ => hWS w) (fun t ht => ?_) (fun t ht => ?_)
    · by_cases hA : glArch (𝓞 K) K t ∈ Ca
      · by_cases hB : ∀ w ∈ S, finComponent (𝓞 K) K w (glFin (𝓞 K) K t) ∈ localIntegralSet K w
        · have hBox : t ∈ Box := ⟨hA, fun w => by
            by_cases hw : w ∈ S
            · exact hB w hw
            · exact ht w hw⟩
          have h1 : W t = 1 := Set.indicator_of_mem hBox _
          have h2 : Wa (glArch (𝓞 K) K t) = 1 := Set.indicator_of_mem hA _
          have h3 : ∀ w ∈ S, WS w (finComponent (𝓞 K) K w (glFin (𝓞 K) K t)) = 1 := fun w hw =>
            Set.indicator_of_mem (hB w hw) _
          rw [h1, h2, Finset.prod_eq_one h3, one_mul]
        · obtain ⟨w, hwS, hw⟩ : ∃ w ∈ S, finComponent (𝓞 K) K w (glFin (𝓞 K) K t) ∉ localIntegralSet K w := by
            by_contra hcon
            exact hB fun w hw => by_contra fun hnot => hcon ⟨w, hw, hnot⟩
          have hBox : t ∉ Box := fun h => hw (h.2 w)
          have h1 : W t = 0 := Set.indicator_of_notMem hBox _
          have h3 : WS w (finComponent (𝓞 K) K w (glFin (𝓞 K) K t)) = 0 := Set.indicator_of_notMem hw _
          rw [h1, Finset.prod_eq_zero hwS h3, mul_zero]
      · have hBox : t ∉ Box := fun h => hA h.1
        have h1 : W t = 0 := Set.indicator_of_notMem hBox _
        have h2 : Wa (glArch (𝓞 K) K t) = 0 := Set.indicator_of_notMem hA _
        rw [h1, h2, zero_mul]
    · obtain ⟨w, -, hw⟩ := ht
      have hBox : t ∉ Box := fun h => hw (h.2 w)
      exact Set.indicator_of_notMem hBox _

  have hIa : ∫ x, Wa x ∂τa = ((τa.real Ca : ℝ) : ℂ) := integral_indicator_one_complex τa hCam
  have hIS : ∀ w, ∫ y, WS w y ∂(τf w) = (((τf w).real (localIntegralSet K w) : ℝ) : ℂ) := fun w =>
    integral_indicator_one_complex (τf w) (measurableSet_localIntegralSet w)
  have h₀ := key S₀ (Finset.Subset.refl S₀)
  have h₁ := key (insert v₀ S₀) (Finset.subset_insert v₀ S₀)
  rw [Finset.prod_insert hv₀, h₀] at h₁

  have hX : (cτ : ℂ) * (∫ x, Wa x ∂τa) * ∏ v ∈ S₀, ∫ y, WS v y ∂(τf v) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact_mod_cast hcτ.ne'
    · rw [hIa]
      have : τa.real Ca ≠ 0 := by
        rw [measureReal_def]
        exact ENNReal.toReal_ne_zero.mpr ⟨hCapos.ne', hCatop.ne⟩
      exact_mod_cast this
    · refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
      rw [hIS]
      have : (τf w).real (localIntegralSet K w) ≠ 0 := by
        rw [measureReal_def]
        exact ENNReal.toReal_ne_zero.mpr ⟨(localIntegralSet_pos w (τf w)).ne', (localIntegralSet_lt_top w (τf w)).ne⟩
      exact_mod_cast this
  have hm : ∫ y, WS v₀ y ∂(τf v₀) = 1 := by
    have h₁' : (cτ : ℂ) * (∫ x, Wa x ∂τa) * ∏ v ∈ S₀, ∫ y, WS v y ∂(τf v) =
        ((cτ : ℂ) * (∫ x, Wa x ∂τa) * ∏ v ∈ S₀, ∫ y, WS v y ∂(τf v)) * ∫ y, WS v₀ y ∂(τf v₀) :=
      calc (cτ : ℂ) * (∫ x, Wa x ∂τa) * ∏ v ∈ S₀, ∫ y, WS v y ∂(τf v)
          = (cτ : ℂ) * (∫ x, Wa x ∂τa) * ((∫ y, WS v₀ y ∂(τf v₀)) * ∏ v ∈ S₀, ∫ y, WS v y ∂(τf v)) := h₁
        _ = ((cτ : ℂ) * (∫ x, Wa x ∂τa) * ∏ v ∈ S₀, ∫ y, WS v y ∂(τf v)) * ∫ y, WS v₀ y ∂(τf v₀) := by ring
    exact (mul_eq_left₀ hX).mp h₁'.symm
  rw [hIS] at hm
  have hm' : (τf v₀).real (localIntegralSet K v₀) = 1 := by exact_mod_cast hm
  rw [measureReal_def] at hm'
  exact (ENNReal.toReal_eq_one_iff _).mp hm'

end Local

section Main

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

end Main

end AutomorphicForm.MassReduction
p2m_reactivate "P2MW.S_AutomorphicForm_mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm.MassReduction"
p2m_reactivate "P2MW.S_AutomorphicForm_mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm.MassReduction"

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

set_option maxHeartbeats 16000000 in
open AutomorphicForm.MassReduction in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)

    (τa : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hτa : @Measure.IsHaarMeasure (GL (Fin 2) (InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) τa)
    (τa' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτa' : τa'.IsHaarMeasure)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (hτf : ∀ v, @Measure.IsHaarMeasure (GL (Fin 2) (v.adicCompletion K)) _ _
      (AutomorphicForm.localGLBorel K v) (τf v))
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτf' : ∀ v, (τf' v).IsHaarMeasure)

    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
      ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
        (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal),
        s ≠ 0 ∧ s ≠ ⊤ ∧
        LinearIndependent ℝ e₁ ∧
          (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
              Y.map (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) ∧
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
            (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
              (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) τa =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                Measure.map (fun c : Fin n₁ → ℝ => ∑ i, c i • e₁ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))

    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
              (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (τf v)) ∨
      ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ∧
       τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        τf v (AutomorphicForm.localIntegralSet K v) +
          τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}))

    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (τ : Measure (Subgroup.centralizer
      ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    (hτ : τ.IsHaarMeasure) (cτ : ℝ) (hcτ : 0 < cτ)
    (hτprod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] Wa τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (WS v) (τf v)) →
        (∀ t : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (t : GL (Fin 2) (AdeleRing (𝓞 K) K))) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K (t : GL (Fin 2) (AdeleRing (𝓞 K) K))) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (t : GL (Fin 2) (AdeleRing (𝓞 K) K))))) →
        (∀ t : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (t : GL (Fin 2) (AdeleRing (𝓞 K) K))) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cτ * (∫ x, Wa x ∂τa) * ∏ v ∈ S, ∫ y, WS v y ∂(τf v))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ' : τ'.IsHaarMeasure) (cτ' : ℝ) (hcτ' : 0 < cτ')
    (hτ'prod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => WS v t) (τf' v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ' = cτ' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))

    (R R' : ENNReal) (hR : R ≠ ⊤) (hR' : R' ≠ ⊤)
    (hD : ∀ D : Set (Subgroup.centralizer
        ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
      IsFundamentalDomain
        (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
          (Subgroup.centralizer
            ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op D τ →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
          (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
          R * ENNReal.ofReal (Real.log (b / a)))
    (hD' : ∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      IsFundamentalDomain
        (((AutomorphicForm.sigmaCentralizer
            (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
          (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
          R' * ENNReal.ofReal (Real.log (b / a))) :
    ENNReal.ofReal cτ' * R = 2 * ENNReal.ofReal cτ * R' := by
  classical
  letI : IsHaarMeasure τa := hτa
  haveI : ∀ v, IsHaarMeasure (τf v) := hτf
  haveI : IsHaarMeasure τ := hτ

  let tloc : HeightOneSpectrum (𝓞 K) → ℝ≥0∞ := fun v => τf v (AutomorphicForm.localIntegralSet K v)

  have hτprodG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
      ∀ (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
      (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
      AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] Wa τa →
      (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (WS v) (τf v)) →
      (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
            AutomorphicForm.localIntegralSet K v) →
          W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
            ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
      (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
            AutomorphicForm.localIntegralSet K v) → W t = 0) →
        ∫ t, W t ∂(τG u τ) = cτ * (∫ x, Wa x ∂τa) * ∏ v ∈ S, ∫ y, WS v y ∂(τf v) := by
    intro S hS W Wa WS hWa hWS hfac hzero
    rw [integral_τG]
    exact hτprod S hS W Wa WS hWa hWS (fun t ht => hfac (t : Gad K) ht) (fun t ht => hzero (t : Gad K) ht)
  have hDG : ∀ D : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)),
      IsFundamentalDomain ((AutomorphicForm.globalPoints (𝓞 K) K).range).op D (τG u τ) →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τG u τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det t) ∈ Set.Icc a b}) =
          R * ENNReal.ofReal (Real.log (b / a)) := by
    intro D hFD a b ha hab
    rw [τG_apply, Set.preimage_inter]
    exact hD _ (isFundamentalDomain_preimage u τ hFD) a b ha hab
  have ht1 : ∀ v ∉ S₀, tloc v = 1 := fun v hv =>
    localMass_eq_one_of_prod τa τf S₀ (τG u τ) cτ hcτ hτprodG v hv

  obtain ⟨n₁, n₂, e₁, e₂, s, hs0, hstop, hli₁, hsp₁, hli₂, hsp₂, hmap₁, hmap₂⟩ := harch
  obtain ⟨e', hli', hsp', hmap'⟩ :=
    AutomorphicForm.exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two
      K L h2 τa n₁ e₁ s ⟨hli₁, hsp₁, hmap₁⟩

  have hGL := AutomorphicForm.rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_globalPoints_inter_ideleNorm_det_Icc
    K τa hτa τf hτf n₁ e' (2 ^ (2 * Module.finrank ℚ K) * s) ⟨hli', hsp', hmap'⟩ S₀ (τG u τ) inferInstance
    cτ hcτ hτprodG R hDG

  have hfin' : ∀ v : HeightOneSpectrum (𝓞 K),
      (∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
              (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          tloc v • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)) ∨
      ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ∧
       τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        tloc v +
          τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}) := by
    intro v
    rcases hfin v with ⟨y, hyN, hymap⟩ | ⟨hkind, hrule⟩
    · refine Or.inl ⟨y, hyN, ?_⟩
      rw [hymap]
      conv_lhs => rw [eq_smul_localHaar v (τf v)]
      rw [Measure.map_smul]
    · exact Or.inr ⟨hkind, hrule⟩

  have hDA := AutomorphicForm.two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
    K L h2 σ hgen δ₀ c u hN hns τa' hτa' τf' hτf' s ⟨n₂, e₂, hli₂, hsp₂, hmap₂⟩ tloc S₀ ht1 hfin' τ' hτ' cτ' hcτ'
    hτ'prod R' hD'

  set V : ℝ≥0∞ := ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
    NumberField.dedekindZeta_residue K) with hV
  set P : ℝ≥0∞ := ∏ v ∈ S₀, tloc v with hP
  calc ENNReal.ofReal cτ' * R
      = ENNReal.ofReal cτ' * (ENNReal.ofReal cτ * (2 ^ (2 * Module.finrank ℚ K) * s) * P * V) := by rw [hGL]
    _ = ENNReal.ofReal cτ * (ENNReal.ofReal cτ' * s * 2 ^ (2 * Module.finrank ℚ K) * P * V) := by ring
    _ = ENNReal.ofReal cτ * (2 * R') := by rw [hDA]
    _ = 2 * ENNReal.ofReal cτ * R' := by ring

end S_AutomorphicForm_mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two (solution)
