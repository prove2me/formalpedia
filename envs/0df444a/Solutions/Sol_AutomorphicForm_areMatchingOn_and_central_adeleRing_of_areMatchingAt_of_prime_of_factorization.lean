-- Prove2me | solution 1 for AutomorphicForm.areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ea877b21-c524-5a1a-87a6-9e56e2b34b51

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
import Theorems.Thm_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
import Theorems.Thm_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
import Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization
import Theorems.Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization
import Theorems.Thm_AutomorphicForm_exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing
import Theorems.Thm_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime
import Theorems.Thm_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_areMatchingLocal
import Theorems.Thm_AutomorphicForm_apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups"
p2m_attr_erase "instance" "ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply Rep.coe_invariantsMap_apply"
p2m_attr_erase "simp" "Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl"
p2m_attr_erase "simp" "LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk"
p2m_attr_erase "simp" "groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.cpowChar_apply_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set
open NumberField.AdelicLevel NumberField.AdelicHaar TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal Classical

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "tensorArch tensorPlace baseChangeGL tensorArch_toTensorGL tensorPlace_toTensorGL tensorArch_sigmaGL tensorPlace_sigmaGL isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf centralizerBorel toTensorGL semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsOrbitalIntegralOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn IsTwistedOrbitalIntegral AreMatchingLocal archHaarK archHaarL archIdentGL AreMatchingArch IsSemiLocalFactorization IsUnitFactorization AreMatchingAt localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet localGLBorel locallyCompactSpace_localGL localHaar localCentralizer IsOrbitalIntegral IsRegularSemisimple AdelicGL2 globalPoints centralScalar sigmaCentralizer mem_sigmaCentralizer_iff exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_areMatchingLocal apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime"
namespace AdelicMatchingCentralExplicitAssembly
p2m_open "AutomorphicForm~continuous_sigmaTensor"

section Generic

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem isRegularSemisimple_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {g : GL (Fin 2) R} (hg : IsRegularSemisimple g) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map f g) := by
  unfold IsRegularSemisimple at hg ⊢
  have hval : ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      f.mapMatrix (g : Matrix (Fin 2) (Fin 2) R) := rfl
  rw [hval, ← RingHom.map_det, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]
  have := hg.map f
  simpa [map_ofNat] using this

theorem map_normString {A B : Type} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (σ : L ≃ₐ[K] L) (F : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B))
    (hF : ∀ x, F (sigmaGL K L A σ x) = sigmaGL K L B σ (F x)) (δ : GL (Fin 2) (L ⊗[K] A)) :
    F (normString K L A σ δ) = normString K L B σ (F δ) := by
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show F ((sigmaGL K L A σ)^[i] δ) = (sigmaGL K L B σ)^[i] (F δ)
  exact (Function.Semiconj.iterate_right (f := F) (ga := sigmaGL K L A σ) (gb := sigmaGL K L B σ) hF i δ)

theorem isNormConjugator_map {A B : Type} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (σ : L ≃ₐ[K] L) (F : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B)) (Fb : GL (Fin 2) A →* GL (Fin 2) B)
    (hF : ∀ x, F (sigmaGL K L A σ x) = sigmaGL K L B σ (F x))
    (hFt : ∀ g, F (toTensorGL K L A g) = toTensorGL K L B (Fb g))
    {γ : GL (Fin 2) A} {δ y : GL (Fin 2) (L ⊗[K] A)} (hy : IsNormConjugator K L A σ γ δ y) :
    IsNormConjugator K L B σ (Fb γ) (F δ) (F y) := by
  unfold IsNormConjugator at hy ⊢
  rw [← hFt, hy, map_mul, map_mul, map_inv, map_normString σ F hF]

end Generic

section Scaling

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  {A : Type} [CommRing A] [Algebra K A] [TopologicalSpace A] {σ : L ≃ₐ[K] L}

theorem isTwistedOrbitalIntegralOn_smul {μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))}
    {δ : GL (Fin 2) (L ⊗[K] A)}
    {τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)}
    {φ : GL (Fin 2) (L ⊗[K] A) → ℂ} {I : ℂ} (h : IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I)
    (a : ℝ≥0) (ha : a ≠ 0) :
    IsTwistedOrbitalIntegralOn K L A σ μ δ (a • τ') φ ((a : ℂ)⁻¹ * I) := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  letI : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  obtain ⟨w, ⟨hw0, hwm, hws, hw1⟩, rfl⟩ := h
  refine ⟨fun x => (a : ℝ)⁻¹ * w x, ⟨fun x => mul_nonneg (inv_nonneg.2 a.2) (hw0 x),
    measurable_const.mul hwm, hws.mul_left, fun x hx => ?_⟩, ?_⟩
  · have h1 := hw1 x hx
    rw [integral_smul_nnreal_measure, integral_const_mul, h1, mul_one, NNReal.smul_def, smul_eq_mul,
      mul_inv_cancel₀ (NNReal.coe_ne_zero.2 ha)]
  · rw [← integral_const_mul]
    congr 1
    funext x
    push_cast
    ring

theorem isTwistedOrbitalIntegralOn_zero_of_forall
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    {φ : GL (Fin 2) (L ⊗[K] A) → ℂ} (h : ∀ x, φ (x⁻¹ * δ * sigmaGL K L A σ x) = 0) :
    IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ 0 :=
  ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun x hx => absurd (h x) hx⟩,
    by simp [h]⟩

theorem isOrbitalIntegralOn_zero_of_forall {A : Type} [CommRing A] [TopologicalSpace A]
    (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    {f : GL (Fin 2) A → ℂ} (h : ∀ x, f (x⁻¹ * γ * x) = 0) :
    IsOrbitalIntegralOn A μ γ τ f 0 :=
  ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun x hx => absurd (h x) hx⟩,
    by simp [h]⟩

end Scaling

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Garch (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (InfiniteAdeleRing K)

abbrev Gad (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (AdeleRing (𝓞 K) K)

abbrev Gv (v : HeightOneSpectrum (𝓞 K)) : Type := GL (Fin 2) (v.adicCompletion K)

abbrev SL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type := L ⊗[K] v.adicCompletion K

abbrev Gsl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type := GL (Fin 2) (SL K L v)

abbrev Gt (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)

abbrev Ht (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)

section Instances

scoped instance instLocallyCompactGarch : LocallyCompactSpace (Garch K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance instLocallyCompactGv (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gv (K := K) v) :=
  locallyCompactSpace_localGL K v

scoped instance instT2Garch : T2Space (Garch K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  exact Units.isEmbedding_embedProduct.t2Space

scoped instance instT2Gv (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gv (K := K) v) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → v.adicCompletion K))
  exact Units.isEmbedding_embedProduct.t2Space

scoped instance instT2Gad : T2Space (Gad K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  exact Units.isEmbedding_embedProduct.t2Space

scoped instance instIsTopologicalRingSL (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalRing (SL K L v) :=
  isTopologicalRing_tensor K L _
scoped instance instT2SL (v : HeightOneSpectrum (𝓞 K)) : T2Space (SL K L v) := t2Space_tensor K L _
scoped instance instLocallyCompactSL (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (SL K L v) :=
  locallyCompactSpace_tensor K L _
scoped instance instLocallyCompactGsl (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gsl K L v) :=
  locallyCompactSpace_tensorGL K L _
scoped instance instIsTopologicalGroupGsl (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalGroup (Gsl K L v) :=
  isTopologicalGroup_tensorGL K L _
scoped instance instT2Gsl (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gsl K L v) := t2Space_tensorGL K L _
scoped instance instIsTopologicalRingTA : IsTopologicalRing (L ⊗[K] AdeleRing (𝓞 K) K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TA : T2Space (L ⊗[K] AdeleRing (𝓞 K) K) := t2Space_tensor K L _
scoped instance instIsTopologicalGroupGt : IsTopologicalGroup (Gt K L) := isTopologicalGroup_tensorGL K L _
scoped instance instT2Gt : T2Space (Gt K L) := t2Space_tensorGL K L _
scoped instance instIsTopologicalRingTI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TI : T2Space (L ⊗[K] InfiniteAdeleRing K) := t2Space_tensor K L _
scoped instance instIsTopologicalGroupHt : IsTopologicalGroup (Ht K L) := isTopologicalGroup_tensorGL K L _
scoped instance instLocallyCompactHt : LocallyCompactSpace (Ht K L) := locallyCompactSpace_tensorGL K L _
scoped instance instT2Ht : T2Space (Ht K L) := t2Space_tensorGL K L _

scoped instance instMeasurableSpaceGarch : MeasurableSpace (Garch K) := borel _
scoped instance instBorelSpaceGarch : BorelSpace (Garch K) := ⟨rfl⟩
scoped instance instMeasurableSpaceGv (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gv (K := K) v) := borel _
scoped instance instBorelSpaceGv (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gv (K := K) v) := ⟨rfl⟩
scoped instance instMeasurableSpaceGad : MeasurableSpace (Gad K) := borel _
scoped instance instBorelSpaceGad : BorelSpace (Gad K) := ⟨rfl⟩
scoped instance instMeasurableSpaceHt : MeasurableSpace (Ht K L) := borel _
scoped instance instBorelSpaceHt : BorelSpace (Ht K L) := ⟨rfl⟩
scoped instance instMeasurableSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gsl K L v) := borel _
scoped instance instBorelSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gsl K L v) := ⟨rfl⟩
scoped instance instMeasurableSpaceGt : MeasurableSpace (Gt K L) := borel _
scoped instance instBorelSpaceGt : BorelSpace (Gt K L) := ⟨rfl⟩

scoped instance (priority := 10000) instMeasurableSpaceSubgroupGad (H : Subgroup (Gad K)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupGad (H : Subgroup (Gad K)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGarch (H : Subgroup (Garch K)) :
    MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGarch (H : Subgroup (Garch K)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGv (v : HeightOneSpectrum (𝓞 K))
    (H : Subgroup (Gv (K := K) v)) : MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGv (v : HeightOneSpectrum (𝓞 K)) (H : Subgroup (Gv (K := K) v)) :
    BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGt (H : Subgroup (Gt K L)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupGt (H : Subgroup (Gt K L)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupHt (H : Subgroup (Ht K L)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupHt (H : Subgroup (Ht K L)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGsl (v : HeightOneSpectrum (𝓞 K))
    (H : Subgroup (Gsl K L v)) : MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGsl (v : HeightOneSpectrum (𝓞 K)) (H : Subgroup (Gsl K L v)) :
    BorelSpace H := ⟨rfl⟩

end Instances

section TorusMeasures

abbrev cpt (v : HeightOneSpectrum (𝓞 K)) (g : Gad K) : Gv (K := K) v := finComponent (𝓞 K) K v (glFin (𝓞 K) K g)

variable (K) in

def unitTorusMeasure (v : HeightOneSpectrum (𝓞 K)) (g : Gv (K := K) v) : Measure (localCentralizer K v g) :=
  haarMeasure
    { carrier := Subtype.val ⁻¹' localIntegralSet K v
      isCompact' := by
        have hcl : IsClosed ((localCentralizer K v g : Subgroup (Gv v)) : Set (Gv v)) := by
          show IsClosed (Set.centralizer ({g} : Set (Gv v)))
          exact Set.isClosed_centralizer _
        exact (Topology.IsClosedEmbedding.subtypeVal hcl).isCompact_preimage (isCompact_localIntegralSet K v)
      interior_nonempty' := by
        rw [((isOpen_localIntegralSet K v).preimage continuous_subtype_val).interior_eq]
        exact ⟨1, one_mem_localIntegralSet K v⟩ }

scoped instance isHaarMeasure_unitTorusMeasure (v : HeightOneSpectrum (𝓞 K)) (g : Gv (K := K) v) :
    IsHaarMeasure (unitTorusMeasure K v g) := by
  haveI : LocallyCompactSpace (localCentralizer K v g) := by
    have hcl : IsClosed ((localCentralizer K v g : Subgroup (Gv v)) : Set (Gv v)) := by
      show IsClosed (Set.centralizer ({g} : Set (Gv v)))
      exact Set.isClosed_centralizer _
    exact hcl.locallyCompactSpace
  unfold unitTorusMeasure
  exact isHaarMeasure_haarMeasure _

theorem unitTorusMeasure_self (v : HeightOneSpectrum (𝓞 K)) (g : Gv (K := K) v) :
    unitTorusMeasure K v g (Subtype.val ⁻¹' localIntegralSet K v) = 1 := by
  unfold unitTorusMeasure
  exact haarMeasure_self

def archTorusMeasure (g : Garch K) : Measure (Subgroup.centralizer ({g} : Set (Garch K))) :=
  haveI : LocallyCompactSpace (Subgroup.centralizer ({g} : Set (Garch K))) := by
    have hcl : IsClosed ((Subgroup.centralizer ({g} : Set (Garch K)) : Subgroup (Garch K)) : Set (Garch K)) := by
      show IsClosed (Set.centralizer ({g} : Set (Garch K)))
      exact Set.isClosed_centralizer _
    exact hcl.locallyCompactSpace
  Measure.haar

scoped instance isHaarMeasure_archTorusMeasure (g : Garch K) : IsHaarMeasure (archTorusMeasure g) := by
  haveI : LocallyCompactSpace (Subgroup.centralizer ({g} : Set (Garch K))) := by
    have hcl : IsClosed ((Subgroup.centralizer ({g} : Set (Garch K)) : Subgroup (Garch K)) : Set (Garch K)) := by
      show IsClosed (Set.centralizer ({g} : Set (Garch K)))
      exact Set.isClosed_centralizer _
    exact hcl.locallyCompactSpace
  unfold archTorusMeasure
  exact isHaarMeasure_haarMeasure _

variable (K L) in

theorem continuous_sigmaTensor (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L) : Continuous (sigmaTensor K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  exact IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap

variable (K L) in
theorem continuous_sigmaGL (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L) : Continuous (sigmaGL K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

variable (K L) in
theorem isClosed_twistedCentralizer (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv
  have : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

variable (σ : L ≃ₐ[K] L)

def unitTwistedTorusMeasure (v : HeightOneSpectrum (𝓞 K)) (d : Gsl K L v) :
    Measure (twistedCentralizer K L (v.adicCompletion K) σ d) :=
  haarMeasure
    { carrier := Subtype.val ⁻¹' semiLocalIntegralSet K L v
      isCompact' :=
        (Topology.IsClosedEmbedding.subtypeVal (isClosed_twistedCentralizer K L _ σ d)).isCompact_preimage
          (isCompact_semiLocalIntegralSet K L v)
      interior_nonempty' := by
        rw [((isOpen_semiLocalIntegralSet K L v).preimage continuous_subtype_val).interior_eq]
        exact ⟨1, one_mem_semiLocalIntegralSet K L v⟩ }

scoped instance isHaarMeasure_unitTwistedTorusMeasure (v : HeightOneSpectrum (𝓞 K)) (d : Gsl K L v) :
    IsHaarMeasure (unitTwistedTorusMeasure σ v d) := by
  haveI : LocallyCompactSpace (twistedCentralizer K L (v.adicCompletion K) σ d) :=
    (isClosed_twistedCentralizer K L _ σ d).locallyCompactSpace
  unfold unitTwistedTorusMeasure
  exact isHaarMeasure_haarMeasure _

theorem unitTwistedTorusMeasure_self (v : HeightOneSpectrum (𝓞 K)) (d : Gsl K L v) :
    unitTwistedTorusMeasure σ v d (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1 := by
  unfold unitTwistedTorusMeasure
  exact haarMeasure_self

def archTwistedTorusMeasure (d : Ht K L) : Measure (twistedCentralizer K L (InfiniteAdeleRing K) σ d) :=
  haveI : LocallyCompactSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ d) :=
    (isClosed_twistedCentralizer K L _ σ d).locallyCompactSpace
  Measure.haar

scoped instance isHaarMeasure_archTwistedTorusMeasure (d : Ht K L) : IsHaarMeasure (archTwistedTorusMeasure σ d) := by
  haveI : LocallyCompactSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ d) :=
    (isClosed_twistedCentralizer K L _ σ d).locallyCompactSpace
  unfold archTwistedTorusMeasure
  exact isHaarMeasure_haarMeasure _

end TorusMeasures

section FixedHaar

variable (K L)

theorem isHaarMeasure_archHaarK : IsHaarMeasure (archHaarK K) := by
  unfold archHaarK
  exact isHaarMeasure_haarMeasure _

theorem isHaarMeasure_archHaarL : IsHaarMeasure (archHaarL K L) := by
  unfold archHaarL
  exact isHaarMeasure_haarMeasure _

end FixedHaar

section Assembly

variable (K L)
variable [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ)
  (hσn : σ ^ Module.finrank K L = 1)
  (μL : Measure (Gt K L)) [hμL : IsHaarMeasure μL]
  (c₀ : ℝ≥0) (hc₀ : c₀ ≠ 0) (cG cG' : ℝ) (hcc : (c₀ : ℝ) * cG = cG')

  (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (f : Gad K → ℂ) (fa : Garch K → ℂ) (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ),
      AEStronglyMeasurable fa (archHaarK K) →
      (∀ v ∈ S, AEStronglyMeasurable (fS v) (localHaar K v)) →
      (∀ g : Gad K, (∀ v ∉ S, cpt v g ∈ localIntegralSet K v) → f g = fa (glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (cpt v g)) →
      (∀ g : Gad K, (∃ v ∉ S, cpt v g ∉ localIntegralSet K v) → f g = 0) →
        ∫ g, f g ∂((c₀ : ℝ≥0) • adelicGLHaar (Fin 2) (𝓞 K) K) =
          (((c₀ : ℝ) * cG : ℝ) : ℂ) * (∫ x, fa x ∂(archHaarK K)) * ∏ v ∈ S, ∫ y, fS v y ∂(localHaar K v))
  (hG' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (F : Gt K L → ℂ) (Fa : Ht K L → ℂ) (FS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
      AEStronglyMeasurable Fa (archHaarL K L) →
      (∀ v ∈ S, AEStronglyMeasurable (FS v) (semiLocalHaar K L v)) →
      (∀ x : Gt K L, (∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) →
          F x = Fa (tensorArch K L x) * ∏ v ∈ S, FS v (tensorPlace K L v x)) →
      (∀ x : Gt K L, (∃ v ∉ S, tensorPlace K L v x ∉ semiLocalIntegralSet K L v) → F x = 0) →
        ∫ x, F x ∂μL = cG' * (∫ y, Fa y ∂(archHaarL K L)) * ∏ v ∈ S, ∫ y, FS v y ∂(semiLocalHaar K L v))

  (S' : Finset (HeightOneSpectrum (𝓞 K)))
  (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : Gad K → ℂ)
  (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
  (φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ)
  (fa : Garch K → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
  (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ)
  (hφ : IsSemiLocalFactorization K L S' φ φa φf φS) (hf : IsUnitFactorization K S' f fa ff fS)
  (hArch : AreMatchingArch K L σ φa fa)
  (hLoc : ∀ v ∈ S', AreMatchingLocal K L v σ (φS v) (fS v))
  (hunit : ∀ v ∉ S', AreMatchingLocal K L v σ
    ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((localIntegralSet K v).indicator fun _ => (1 : ℂ)))

def fSp (v : HeightOneSpectrum (𝓞 K)) : Gv (K := K) v → ℂ :=
  if v ∈ S' then fS v else (localIntegralSet K v).indicator fun _ => (1 : ℂ)

def φSp (v : HeightOneSpectrum (𝓞 K)) : Gsl K L v → ℂ :=
  if v ∈ S' then φS v else (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)

omit [IsGalois K L] in
include hLoc hunit in
theorem areMatchingLocal_p (v : HeightOneSpectrum (𝓞 K)) :
    AreMatchingLocal K L v σ (φSp K L S' φS v) (fSp K S' fS v) := by
  by_cases hv : v ∈ S'
  · simp only [φSp, fSp, hv, if_true]; exact hLoc v hv
  · simp only [φSp, fSp, hv, if_false]; exact hunit v hv

omit [IsGalois K L] in

theorem local_compare (v : HeightOneSpectrum (𝓞 K)) (γ : Gad K) (hγ : IsRegularSemisimple γ)
    (δ y : Gt K L) (hδ : IsRegularSemisimple (normString K L (AdeleRing (𝓞 K) K) σ δ))
    (hy : IsNormConjugator K L (AdeleRing (𝓞 K) K) σ γ δ y)
    (τv : Measure (localCentralizer K v (cpt v γ))) [IsHaarMeasure τv]
    (τv' : Measure (twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ))) [IsHaarMeasure τv']
    (a : ℝ≥0) (ha : a ≠ 0)
    (hCv : Coupled K L (v.adicCompletion K) σ (cpt v γ) (tensorPlace K L v δ) (tensorPlace K L v y) τv (a • τv'))
    (hM : AreMatchingLocal K L v σ (φSp K L S' φS v) (fSp K S' fS v))
    {J J' : ℂ} (hJ : IsOrbitalIntegral K v (cpt v γ) τv (fSp K S' fS v) J)
    (hJ' : IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) τv' (φSp K L S' φS v) J') :
    J' = a * J := by
  have hγv : IsRegularSemisimple (cpt v γ) := isRegularSemisimple_map _ (isRegularSemisimple_map _ hγ)
  have hδv : IsRegularSemisimple (normString K L (v.adicCompletion K) σ (tensorPlace K L v δ)) := by
    rw [← map_normString σ (tensorPlace K L v) (tensorPlace_sigmaGL K L σ v) δ]
    exact isRegularSemisimple_map _ hδ
  have hyv : IsNormConjugator K L (v.adicCompletion K) σ (cpt v γ) (tensorPlace K L v δ) (tensorPlace K L v y) :=
    isNormConjugator_map σ (tensorPlace K L v) ((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K))
      (tensorPlace_sigmaGL K L σ v) (tensorPlace_toTensorGL K L v) hy
  haveI : IsHaarMeasure (a • τv') := IsHaarMeasure.nnreal_smul _ ha
  have hJ'' := isTwistedOrbitalIntegralOn_smul hJ' a ha
  have h := hM.1 (tensorPlace K L v δ) hδv (cpt v γ) hγv (tensorPlace K L v y) hyv τv (a • τv')
    inferInstance inferInstance hCv J _ hJ'' hJ
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  calc J' = a * ((a : ℂ)⁻¹ * J') := by field_simp
    _ = a * J := by rw [h]

omit [IsGalois K L] in
include hArch in

theorem arch_compare (γ : Gad K) (hγ : IsRegularSemisimple γ)
    (δ y : Gt K L) (hδ : IsRegularSemisimple (normString K L (AdeleRing (𝓞 K) K) σ δ))
    (hy : IsNormConjugator K L (AdeleRing (𝓞 K) K) σ γ δ y)
    (τa : Measure (Subgroup.centralizer ({glArch (𝓞 K) K γ} : Set (Garch K)))) [IsHaarMeasure τa]
    (τa' : Measure (twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L δ))) [IsHaarMeasure τa']
    (b : ℝ≥0) (hb : b ≠ 0)
    (hCa : Coupled K L (InfiniteAdeleRing K) σ (glArch (𝓞 K) K γ) (tensorArch K L δ) (tensorArch K L y) τa (b • τa'))
    {J J' : ℂ} (hJ : IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) (glArch (𝓞 K) K γ) τa fa J)
    (hJ' : IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) (tensorArch K L δ) τa'
      (φa ∘ archIdentGL K L) J') :
    J' = b * J := by
  have hγa : IsRegularSemisimple (glArch (𝓞 K) K γ) := isRegularSemisimple_map _ hγ
  have hδa : IsRegularSemisimple (normString K L (InfiniteAdeleRing K) σ (tensorArch K L δ)) := by
    rw [← map_normString σ (tensorArch K L) (tensorArch_sigmaGL K L σ) δ]
    exact isRegularSemisimple_map _ hδ
  have hya : IsNormConjugator K L (InfiniteAdeleRing K) σ (glArch (𝓞 K) K γ) (tensorArch K L δ) (tensorArch K L y) :=
    isNormConjugator_map σ (tensorArch K L) (glArch (𝓞 K) K) (tensorArch_sigmaGL K L σ) (tensorArch_toTensorGL K L) hy
  haveI : IsHaarMeasure (b • τa') := IsHaarMeasure.nnreal_smul _ hb
  have hJ'' := isTwistedOrbitalIntegralOn_smul hJ' b hb
  have h := hArch.1 (tensorArch K L δ) hδa (glArch (𝓞 K) K γ) hγa (tensorArch K L y) hya τa (b • τa')
    inferInstance inferInstance hCa J _ hJ'' hJ
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  calc J' = b * ((b : ℂ)⁻¹ * J') := by field_simp
    _ = b * J := by rw [h]

include hgen hσn hc₀ hcc hG hG' hφ hf hArch hLoc hunit in

theorem clause_one (δ : Gt K L) (hδ : IsRegularSemisimple (normString K L (AdeleRing (𝓞 K) K) σ δ))
    (γ : Gad K) (hγ : IsRegularSemisimple γ) (y : Gt K L)
    (hy : IsNormConjugator K L (AdeleRing (𝓞 K) K) σ γ δ y)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (Gad K)))) (τ' : Measure (twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ))
    [IsHaarMeasure τ] [IsHaarMeasure τ'] (hC : Coupled K L (AdeleRing (𝓞 K) K) σ γ δ y τ τ')
    (I I' : ℂ)
    (hI' : IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μL δ τ' (φ ∘ baseChangeGL K L) I')
    (hI : IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) ((c₀ : ℝ≥0) • adelicGLHaar (Fin 2) (𝓞 K) K) γ τ f I) :
    I' = I := by

  set τa := archTorusMeasure (glArch (𝓞 K) K γ) with hτa_def
  set τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (localCentralizer K v (cpt v γ)) :=
    fun v => unitTorusMeasure K v (cpt v γ) with hτf_def
  set τa' := archTwistedTorusMeasure σ (tensorArch K L δ) with hτa'_def
  set τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)) :=
    fun v => unitTwistedTorusMeasure σ v (tensorPlace K L v δ) with hτf'_def
  have hτf1 : ∀ v, τf v (Subtype.val ⁻¹' localIntegralSet K v) = 1 := fun v => unitTorusMeasure_self v _
  have hτf1' : ∀ v, τf' v (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1 :=
    fun v => unitTwistedTorusMeasure_self σ v _

  obtain ⟨cT, hcT, hT⟩ :=
    AutomorphicForm.exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure K γ τ
      inferInstance τa inferInstance τf (fun v => inferInstance) hτf1
  obtain ⟨cT', hcT', hT'⟩ :=
    AutomorphicForm.exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure K L σ δ
      τ' inferInstance τa' inferInstance τf' (fun v => inferInstance) hτf1'

  obtain ⟨a, b, ha, hb, hCv, hCa, S₀, hconst⟩ :=
    AutomorphicForm.exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing K L σ hgen γ hγ δ y hy τ
      τa inferInstance τf (fun v => inferInstance) cT hT τ' τa'
      inferInstance τf' (fun v => inferInstance) hτf1' cT' hT' hC

  haveI : IsHaarMeasure ((c₀ : ℝ≥0) • adelicGLHaar (Fin 2) (𝓞 K) K) :=
    @IsHaarMeasure.nnreal_smul _ _ _ _ _ (isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K) _ hc₀
  have HK := AutomorphicForm.exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization K
    ((c₀ : ℝ≥0) • adelicGLHaar (Fin 2) (𝓞 K) K) inferInstance (archHaarK K) ((c₀ : ℝ) * cG) hG γ hγ τ
    inferInstance τa inferInstance τf (fun v => inferInstance) hτf1 cT hcT hT S' f fa ff fS hf I hI
  have HL := AutomorphicForm.exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization
    K L σ hσn μL hμL (archHaarL K L) cG' hG' δ hδ τ' inferInstance τa' inferInstance τf'
    (fun v => inferInstance) hτf1' cT' hcT' hT' S' φ φa φf φS hφ I' hI'

  have hM := areMatchingLocal_p K L σ S' φS fS hLoc hunit
  have cmp : ∀ v {J J' : ℂ}, IsOrbitalIntegral K v (cpt v γ) (τf v) (fSp K S' fS v) J →
      IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf' v) (φSp K L S' φS v) J' → J' = a v * J :=
    fun v J J' hJ hJ' => local_compare K L σ S' φS fS v γ hγ δ y hδ hy (τf v) (τf' v) (a v) (ha v) (hCv v) (hM v) hJ hJ'
  have cmpa : ∀ {J J' : ℂ}, IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) (glArch (𝓞 K) K γ) τa fa J →
      IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) (tensorArch K L δ) τa'
        (φa ∘ archIdentGL K L) J' → J' = b * J :=
    fun hJ hJ' => arch_compare K L σ φa fa hArch γ hγ δ y hδ hy τa τa' b hb hCa hJ hJ'

  have convK : ∀ (Iv : HeightOneSpectrum (𝓞 K) → ℂ),
      (∀ v ∈ S', IsOrbitalIntegral K v (cpt v γ) (τf v) (fS v) (Iv v)) →
      (∀ v ∉ S', IsOrbitalIntegral K v (cpt v γ) (τf v) ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) (Iv v)) →
      ∀ v, IsOrbitalIntegral K v (cpt v γ) (τf v) (fSp K S' fS v) (Iv v) := by
    intro Iv h1 h2 v
    by_cases hv : v ∈ S'
    · simp only [fSp, hv, if_true]; exact h1 v hv
    · simp only [fSp, hv, if_false]; exact h2 v hv
  have convL : ∀ (Iv : HeightOneSpectrum (𝓞 K) → ℂ),
      (∀ v ∈ S', IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf' v) (φS v) (Iv v)) →
      (∀ v ∉ S', IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf' v)
        ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) (Iv v)) →
      ∀ v, IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf' v) (φSp K L S' φS v) (Iv v) := by
    intro Iv h1 h2 v
    by_cases hv : v ∈ S'
    · simp only [φSp, hv, if_true]; exact h1 v hv
    · simp only [φSp, hv, if_false]; exact h2 v hv

  have emptyK : ((∃ v ∈ S', ∀ x : Gv (K := K) v, fS v (x⁻¹ * cpt v γ * x) = 0) ∨
        (∃ v ∉ S', ∀ x : Gv (K := K) v, x⁻¹ * cpt v γ * x ∉ localIntegralSet K v)) →
      ∃ v, IsOrbitalIntegral K v (cpt v γ) (τf v) (fSp K S' fS v) 0 := by
    rintro (⟨v, hv, h⟩ | ⟨v, hv, h⟩)
    · refine ⟨v, ?_⟩
      simp only [fSp, hv, if_true]
      exact isOrbitalIntegralOn_zero_of_forall _ _ _ h
    · refine ⟨v, ?_⟩
      simp only [fSp, hv, if_false]
      exact isOrbitalIntegralOn_zero_of_forall _ _ _ fun x => Set.indicator_of_notMem (h x) _
  have emptyL : ((∃ v ∈ S', ∀ x : Gsl K L v, φS v (x⁻¹ * tensorPlace K L v δ * sigmaGL K L (v.adicCompletion K) σ x) = 0) ∨
        (∃ v ∉ S', ∀ x : Gsl K L v, x⁻¹ * tensorPlace K L v δ * sigmaGL K L (v.adicCompletion K) σ x ∉
          semiLocalIntegralSet K L v)) →
      ∃ v, IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf' v) (φSp K L S' φS v) 0 := by
    rintro (⟨v, hv, h⟩ | ⟨v, hv, h⟩)
    · refine ⟨v, ?_⟩
      simp only [φSp, hv, if_true]
      exact isTwistedOrbitalIntegralOn_zero_of_forall _ _ _ h
    · refine ⟨v, ?_⟩
      simp only [φSp, hv, if_false]
      exact isTwistedOrbitalIntegralOn_zero_of_forall _ _ _ fun x => Set.indicator_of_notMem (h x) _
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have ha' : ∀ v, ((a v : ℝ) : ℂ) ≠ 0 := fun v => by exact_mod_cast ha v

  rcases HK with ⟨hI0, hKe⟩ | ⟨S₁, hSS₁, Ia, Iv, hIa, hIvS, hIvnS, hIeq⟩ <;>
    rcases HL with ⟨hI'0, hLe⟩ | ⟨S₁', hSS₁', Ia', Iv', hIa', hIv'S, hIv'nS, hI'eq⟩
  ·
    rw [hI0, hI'0]
  ·
    rw [hI0]
    have hIv' := convL Iv' hIv'S hIv'nS
    rcases hKe with hKa | hKf
    ·
      have h0 : Ia' = 0 := by
        have := cmpa (isOrbitalIntegralOn_zero_of_forall _ _ _ hKa) hIa'
        rw [this, mul_zero]
      rw [hI'eq S₁' (Finset.Subset.refl _), h0]; ring
    · obtain ⟨v₀, hv₀⟩ := emptyK hKf
      have h0 : Iv' v₀ = 0 := by
        have := cmp v₀ hv₀ (hIv' v₀)
        rw [this, mul_zero]
      rw [hI'eq (insert v₀ S₁') (Finset.subset_insert _ _),
        Finset.prod_eq_zero (Finset.mem_insert_self v₀ S₁') h0]
      ring
  ·
    rw [hI'0]
    have hIv := convK Iv hIvS hIvnS
    rcases hLe with hLa | hLf
    · have h0 : Ia = 0 := by
        have := cmpa hIa (isTwistedOrbitalIntegralOn_zero_of_forall _ _ _ hLa)
        exact (mul_eq_zero.1 this.symm).resolve_left hb'
      rw [hIeq S₁ (Finset.Subset.refl _), h0]; ring
    · obtain ⟨v₀, hv₀⟩ := emptyL hLf
      have h0 : Iv v₀ = 0 := by
        have := cmp v₀ (hIv v₀) hv₀
        exact (mul_eq_zero.1 this.symm).resolve_left (ha' v₀)
      rw [hIeq (insert v₀ S₁) (Finset.subset_insert _ _),
        Finset.prod_eq_zero (Finset.mem_insert_self v₀ S₁) h0]
      ring
  ·
    have hIv := convK Iv hIvS hIvnS
    have hIv' := convL Iv' hIv'S hIv'nS
    set T := S₁ ∪ S₁' ∪ S₀ with hT_def
    have hT₁ : S₁ ⊆ T := Finset.subset_union_left.trans Finset.subset_union_left
    have hT₁' : S₁' ⊆ T := Finset.subset_union_right.trans Finset.subset_union_left
    have hT₀ : S₀ ⊆ T := Finset.subset_union_right
    have e1 := hIeq T hT₁
    have e2 := hI'eq T hT₁'
    have e3 := hconst T hT₀
    have e4 : Ia' = b * Ia := cmpa hIa hIa'
    have e5 : ∀ v, Iv' v = a v * Iv v := fun v => cmp v (hIv v) (hIv' v)
    have e6 : ∏ v ∈ T, Iv' v = (∏ v ∈ T, ((a v : ℝ) : ℂ)) * ∏ v ∈ T, Iv v := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => e5 v
    have hprod : (∏ v ∈ T, ((a v : ℝ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => ha' v
    have hcT0 : (cT : ℂ) ≠ 0 := by exact_mod_cast hcT.ne'
    rw [e2, e1, e6, e4, e3, ← hcc]
    push_cast
    field_simp

omit [IsGalois K L] in
include hc₀ hG hf hArch hLoc hunit in

theorem clause_two (hprime : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (γ : Gad K) (hγ : IsRegularSemisimple γ)
    (hno : ¬ ∃ δ, IsNormOf K L (AdeleRing (𝓞 K) K) σ γ δ)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (Gad K)))) [IsHaarMeasure τ] (I : ℂ)
    (hI : IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) ((c₀ : ℝ≥0) • adelicGLHaar (Fin 2) (𝓞 K) K) γ τ f I) :
    I = 0 := by
  set τa := archTorusMeasure (glArch (𝓞 K) K γ) with hτa_def
  set τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (localCentralizer K v (cpt v γ)) :=
    fun v => unitTorusMeasure K v (cpt v γ) with hτf_def
  have hτf1 : ∀ v, τf v (Subtype.val ⁻¹' localIntegralSet K v) = 1 := fun v => unitTorusMeasure_self v _
  obtain ⟨cT, hcT, hT⟩ :=
    AutomorphicForm.exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure K γ τ
      inferInstance τa inferInstance τf (fun v => inferInstance) hτf1
  haveI : IsHaarMeasure ((c₀ : ℝ≥0) • adelicGLHaar (Fin 2) (𝓞 K) K) :=
    @IsHaarMeasure.nnreal_smul _ _ _ _ _ (isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K) _ hc₀
  have HK := AutomorphicForm.exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization K
    ((c₀ : ℝ≥0) • adelicGLHaar (Fin 2) (𝓞 K) K) inferInstance (archHaarK K) ((c₀ : ℝ) * cG) hG γ hγ τ
    inferInstance τa inferInstance τf (fun v => inferInstance) hτf1 cT hcT hT S' f fa ff fS hf I hI
  rcases HK with ⟨hI0, -⟩ | ⟨S₁, hSS₁, Ia, Iv, hIa, hIvS, hIvnS, hIeq⟩
  · exact hI0
  have hM := areMatchingLocal_p K L σ S' φS fS hLoc hunit
  have hIv : ∀ v, IsOrbitalIntegral K v (cpt v γ) (τf v) (fSp K S' fS v) (Iv v) := by
    intro v
    by_cases hv : v ∈ S'
    · simp only [fSp, hv, if_true]; exact hIvS v hv
    · simp only [fSp, hv, if_false]; exact hIvnS v hv

  by_cases harch : ∃ δa : Ht K L, IsNormOf K L (InfiniteAdeleRing K) σ (glArch (𝓞 K) K γ) δa
  · by_cases hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ δv : Gsl K L v,
        IsNormOf K L (v.adicCompletion K) σ (cpt v γ) δv
    · exact absurd (AutomorphicForm.exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime K L hprime σ hσ1
        γ hγ hfin harch) hno
    · push Not at hfin
      obtain ⟨v₀, hv₀⟩ := hfin
      have hno₀ : ¬ ∃ δv : Gsl K L v₀, IsNormOf K L (v₀.adicCompletion K) σ (cpt v₀ γ) δv := fun ⟨d, hd⟩ => hv₀ d hd
      have h0 : Iv v₀ = 0 :=
        (hM v₀).2 (cpt v₀ γ) (isRegularSemisimple_map _ (isRegularSemisimple_map _ hγ)) hno₀ (τf v₀) inferInstance
          (Iv v₀) (hIv v₀)
      rw [hIeq (insert v₀ S₁) (Finset.subset_insert _ _), Finset.prod_eq_zero (Finset.mem_insert_self v₀ S₁) h0]
      ring
  · have h0 : Ia = 0 := hArch.2 (glArch (𝓞 K) K γ) (isRegularSemisimple_map _ hγ) harch τa inferInstance Ia hIa
    rw [hIeq S₁ (Finset.Subset.refl _), h0]; ring

end Assembly

end AutomorphicForm.AdelicMatchingCentralExplicitAssembly
p2m_reactivate "P2MW.S_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization.AutomorphicForm P2MW.S_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization.AutomorphicForm.AdelicMatchingCentralExplicitAssembly"
p2m_reactivate "P2MW.S_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization.AutomorphicForm P2MW.S_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization.AutomorphicForm.AdelicMatchingCentralExplicitAssembly"

p2m_open "AutomorphicForm~continuous_sigmaTensor" in open _root_.P2MW.S_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization.AutomorphicForm AutomorphicForm.AdelicMatchingCentralExplicitAssembly in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μL)

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
          ∫ x, F x ∂μL = cL * (∫ y, Fa y ∂(AutomorphicForm.archHaarL K L)) * ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))
    (c₀ : NNReal) (hc₀ : (c₀ : ℝ) * cK = cL) :
      ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
      ∀ (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ),
        AutomorphicForm.AreMatchingAt K L σ S' φ f →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) →
        AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ μL
          (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (φ ∘ Matrix.GeneralLinearGroup.map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
          f ∧
        (∀ (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
          AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
            AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
              (AutomorphicForm.centralScalar (𝓞 K) K u) →
          ∀ (τ : Measure (Subgroup.centralizer
              ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
            (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
            τ.IsHaarMeasure → τ'.IsHaarMeasure →
          ∀ C : ENNReal, C ≠ 0 → C ≠ ⊤ →
            (∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
                (Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                  Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
              IsFundamentalDomain
                (((AutomorphicForm.sigmaCentralizer
                    (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
                    (Matrix.GeneralLinearGroup.map
                      (Algebra.TensorProduct.includeLeftRingHom :
                        L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
                  (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
                    (Matrix.GeneralLinearGroup.map
                        (Algebra.TensorProduct.includeLeftRingHom :
                          L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                      Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
              ∀ a b : ℝ, 0 < a → a ≤ b →
                τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
                  (Matrix.GeneralLinearGroup.det
                    (Matrix.GeneralLinearGroup.map
                      (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                        (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                      (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
                  C * ENNReal.ofReal (Real.log (b / a))) →
            (∀ D : Set (Subgroup.centralizer
                ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
              IsFundamentalDomain
                (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
                  (Subgroup.centralizer
                    ({AutomorphicForm.centralScalar (𝓞 K) K u} :
                      Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op D τ →
              ∀ a b : ℝ, 0 < a → a ≤ b →
                τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
                  (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 K) K)) ∈
                    Set.Icc a b}) =
                  (Module.finrank K L : ENNReal) * C * ENNReal.ofReal (Real.log (b / a))) →
          ∀ I I' : ℂ,
            AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μL
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ'
              (φ ∘ Matrix.GeneralLinearGroup.map
                (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                  (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) I' →
            AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K)
              (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
              (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I → I' = I) ∧
        (∀ u : (AdeleRing (𝓞 K) K)ˣ,
          (¬ ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
              AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ
                (AutomorphicForm.centralScalar (𝓞 K) K u) δ) →
          ∀ τ : Measure (Subgroup.centralizer
              ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
            τ.IsHaarMeasure →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K)
              (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
              (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I → I = 0) := by

  obtain ⟨hGal, hord, htop⟩ := AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hprime σ hσ
  haveI := hGal
  have hgen : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ := fun θ => by rw [htop]; exact Subgroup.mem_top θ
  have hσn : σ ^ Module.finrank K L = 1 := by rw [← hord]; exact pow_orderOf_eq_one σ

  haveI hμK : IsHaarMeasure (adelicGLHaar (Fin 2) (𝓞 K) K) := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := hμL
  haveI := isHaarMeasure_archHaarK K
  haveI := isHaarMeasure_archHaarL K L

  have hcc : (c₀ : ℝ) * cK = cL := hc₀
  have hc₀ne : c₀ ≠ 0 := by
    intro h
    have h0 : (c₀ : ℝ) = 0 := by rw [h]; rfl
    have : cL = 0 := by rw [← hcc, h0, zero_mul]
    exact hcL.ne' this

  have hG₀ : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (f : Gad K → ℂ) (fa : Garch K → ℂ) (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ),
      AEStronglyMeasurable fa (archHaarK K) →
      (∀ v ∈ S, AEStronglyMeasurable (fS v) (localHaar K v)) →
      (∀ g : Gad K, (∀ v ∉ S, cpt v g ∈ localIntegralSet K v) → f g = fa (glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (cpt v g)) →
      (∀ g : Gad K, (∃ v ∉ S, cpt v g ∉ localIntegralSet K v) → f g = 0) →
        ∫ g, f g ∂((c₀ : ℝ≥0) • adelicGLHaar (Fin 2) (𝓞 K) K) =
          (((c₀ : ℝ) * cK : ℝ) : ℂ) * (∫ x, fa x ∂(archHaarK K)) * ∏ v ∈ S, ∫ y, fS v y ∂(localHaar K v) := by
    intro S f fa fS h1 h2 h3 h4
    rw [integral_smul_nnreal_measure, hG S f fa fS h1 h2 h3 h4, NNReal.smul_def, Complex.real_smul]
    push_cast
    ring
  intro S' hSK φ f hAt hunit
  obtain ⟨φa, φf, φS, fa, ff, fS, hφ, hf, hArch, hLoc⟩ := hAt
  have hS'' : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' → ∀ w : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1 :=
    fun v hv w hw => hS w (by rw [hw]; exact fun h => hv (hSK h))
  have hunit' : ∀ v ∉ S', AreMatchingLocal K L v σ
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) :=
    fun v hv => hunit v hv (hS'' v hv)
  refine ⟨⟨fun δ hδ γ hγ y hy τ τ' hτ hτ' hC I I' hI' hI => ?_, fun γ hγ hno τ hτ I hI => ?_⟩,
    fun δ₀ c u hN τ τ' hτ hτ' C hC0 hCt hD' hD I I' hI' hI => ?_, fun u hu τ hτ I hI => ?_⟩
  ·
    haveI := hτ; haveI := hτ'
    exact clause_one K L σ hgen hσn μL c₀ hc₀ne cK cL hcc hG₀ hG' S' φ f φa φf φS fa ff fS hφ hf hArch hLoc hunit'
      δ hδ γ hγ y hy τ τ' hC I I' hI' hI
  ·
    haveI := hτ
    exact clause_two K L σ c₀ hc₀ne cK hG₀ S' f φa φS fa ff fS hf hArch hLoc hunit' hprime hσ γ hγ hno τ I hI
  ·
    have hcK₀ : 0 < (c₀ : ℝ) * cK := by rw [hcc]; exact hcL
    haveI hμK₀ : IsHaarMeasure ((c₀ : ℝ≥0) • adelicGLHaar (Fin 2) (𝓞 K) K) :=
      @IsHaarMeasure.nnreal_smul _ _ _ _ _ (isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K) _ hc₀ne
    have key :=
      AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_areMatchingLocal
        K L hprime σ hσ ((c₀ : ℝ≥0) • adelicGLHaar (Fin 2) (𝓞 K) K) hμK₀ μL hμL ((c₀ : ℝ) * cK) cL
        hcK₀ hcL hG₀ hG' S' hS'' φ f φa φf φS fa ff fS hφ hf hArch hLoc hunit' δ₀ c u hN τ τ' hτ hτ'
        C hC0 hCt hD' hD I I' hI' hI
    rw [hcc] at key
    have hne : ((cL : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcL.ne'
    exact mul_left_cancel₀ hne key
  ·
    obtain ⟨w, -, rfl⟩ := hI
    have h0 : f (centralScalar (𝓞 K) K u) = 0 :=
      AutomorphicForm.apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime
        K L hprime σ hσ S' f fa ff fS hf φS hφ.2.2.1 hLoc hunit' u hu
    have hcentral : ∀ x : Gad K, x⁻¹ * centralScalar (𝓞 K) K u * x = centralScalar (𝓞 K) K u := by
      intro x
      have hcomm : centralScalar (𝓞 K) K u * x = x * centralScalar (𝓞 K) K u := by
        refine Units.ext ?_
        show Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K) * (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
          (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K)
        exact (Matrix.scalar_commute (u : AdeleRing (𝓞 K) K) (fun r => Commute.all _ r) _).eq
      rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    simp only [hcentral, h0, zero_mul, integral_zero]

end S_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization
end P2MW
export P2MW.S_AutomorphicForm_areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization (solution)
