-- Prove2me | solution 1 for AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e10920e4-de67-50aa-99cb-d2e4e00ccda7

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_and_isTwistedOrbitalIntegral_eq_mul_apply_scalar_of_normString_eq_toTensorGL_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_finite_and_even_ncard_places_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk groupCohomology.Cores.Transversal.mk.sizeOf_spec"
p2m_attr_erase "simp" "groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.preimage_mulLeft_smul UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicHaar NumberField.AdelicLevel TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "tensorArchHom tensorPlaceHom tensorArchHom_tmul tensorPlaceHom_tmul tensorArch tensorPlace baseChangeGL tensorArch_toTensorGL tensorPlace_toTensorGL tensorArchHom_sigmaTensor tensorPlaceHom_sigmaTensor semiLocalHomeomorph_eq isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf centralizerBorel toTensorGL semiLocalIntegers semiLocalIntegers_eq_preimage IsSemiLocalTestFn semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet isSemiLocalTestFn_indicator_semiLocalIntegralSet semiLocalHaar sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedOrbitalIntegralOn IsTwistedOrbitalIntegral AreMatchingLocal archHaarK archHaarL archIdentGL AreMatchingArch IsSemiLocalFactorization IsUnitFactorization IsLocalTestFn localIntegralSet mem_localIntegralSet isOpen_localIntegralSet isLocalTestFn_indicator_localIntegralSet localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localHaar_localIntegralSet AdelicGL2 globalPoints centralScalar sigmaCentralizer mem_sigmaCentralizer_iff exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure exists_isHaarMeasure_and_isTwistedOrbitalIntegral_eq_mul_apply_scalar_of_normString_eq_toTensorGL_scalar_of_finrank_eq_two twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two finite_and_even_ncard_places_not_isSigmaConjugate_scalar_of_finrank_eq_two mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two"
namespace CentralQuaternion
p2m_open "AutomorphicForm~sigmaTensor_includeRight"

section LinearAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

abbrev sc (c : Rˣ) : GL (Fin 2) R := Matrix.GeneralLinearGroup.scalar (Fin 2) c

theorem scalar_mul_comm (c : Rˣ) (g : GL (Fin 2) R) : sc c * g = g * sc c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (g : Matrix (Fin 2) (Fin 2) R) =
    (g : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

theorem conj_scalar (c : Rˣ) (g : GL (Fin 2) R) : g⁻¹ * sc c * g = sc c := by
  rw [mul_assoc, scalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem centralizer_scalar_eq_top (c : Rˣ) :
    Subgroup.centralizer ({sc c} : Set (GL (Fin 2) R)) = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff, SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  exact (scalar_mul_comm c g).symm

theorem map_scalar (f : R →+* S) (c : Rˣ) :
    Matrix.GeneralLinearGroup.map f (sc c) = sc (Units.map (f : R →* S) c) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show f ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : Matrix (Fin 2) (Fin 2) R) i j) = _
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem sc_mul (c d : Rˣ) : sc (c * d) = sc c * sc d := map_mul _ c d

theorem sc_inv (c : Rˣ) : sc c⁻¹ = (sc c)⁻¹ := map_inv _ c

theorem map_map_gl {T : Type*} [CommRing T] (f : R →+* S) (g : S →+* T) (x : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map g (Matrix.GeneralLinearGroup.map f x) = Matrix.GeneralLinearGroup.map (g.comp f) x := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rfl

theorem map_congr_gl {f g : R →+* S} (h : ∀ r, f r = g r) (x : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map f x = Matrix.GeneralLinearGroup.map g x := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  exact h _

theorem det_map_gl (f : R →+* S) (x : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f x) = Units.map (f : R →* S) (Matrix.GeneralLinearGroup.det x) := by
  refine Units.ext ?_
  show Matrix.det (f.mapMatrix (x : Matrix (Fin 2) (Fin 2) R)) = f (Matrix.det (x : Matrix (Fin 2) (Fin 2) R))
  exact (RingHom.map_det f _).symm

theorem det_sc (c : Rˣ) : Matrix.GeneralLinearGroup.det (sc c) = c * c := by
  refine Units.ext ?_
  show Matrix.det ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = (c : R) * c
  rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (c : R) from rfl, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]

end LinearAlgebra

section Tensor

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_tmul (l : L) (a : A) : sigmaTensor K L A σ (l ⊗ₜ a) = σ l ⊗ₜ a := by
  simp [sigmaTensor]

theorem sigmaTensor_includeRight (a : A) :
    sigmaTensor K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a := by
  simp [sigmaTensor]

theorem sigmaGL_toTensorGL (g : GL (Fin 2) A) : sigmaGL K L A σ (toTensorGL K L A g) = toTensorGL K L A g := by
  ext i j
  change sigmaTensor K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)) =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)
  exact sigmaTensor_includeRight K L σ A _

theorem sigmaGL_map_includeLeft (δ₀ : GL (Fin 2) L) :
    sigmaGL K L A σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
        (Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀) := by
  ext i j
  change sigmaTensor K L A σ (((δ₀ : Matrix (Fin 2) (Fin 2) L) i j) ⊗ₜ[K] (1 : A)) = (σ ((δ₀ : Matrix (Fin 2) (Fin 2) L) i j)) ⊗ₜ[K] (1 : A)
  exact sigmaTensor_tmul K L σ A _ _

theorem coe_toTensorGL (g : GL (Fin 2) A) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (g : Matrix (Fin 2) (Fin 2) A).map (fun a => (1 : L) ⊗ₜ[K] a) := rfl

theorem toTensorGL_scalar (c : Aˣ) :
    toTensorGL K L A (sc c) =
      sc (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom : A →* L ⊗[K] A) c) :=
  map_scalar _ c

theorem map_normString {B : Type} [CommRing B] [Algebra K B] (f : L ⊗[K] A →+* L ⊗[K] B)
    (hf : ∀ z, f (sigmaTensor K L A σ z) = sigmaTensor K L B σ (f z)) (δ : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.map f (normString K L A σ δ) =
      normString K L B σ (Matrix.GeneralLinearGroup.map f δ) := by
  have hcomm : ∀ x : GL (Fin 2) (L ⊗[K] A), Matrix.GeneralLinearGroup.map f (sigmaGL K L A σ x) =
      sigmaGL K L B σ (Matrix.GeneralLinearGroup.map f x) := fun x =>
    Matrix.GeneralLinearGroup.ext fun i j => hf _
  have hiter : ∀ (i : ℕ) (x : GL (Fin 2) (L ⊗[K] A)),
      Matrix.GeneralLinearGroup.map f ((⇑(sigmaGL K L A σ))^[i] x) =
        (⇑(sigmaGL K L B σ))^[i] (Matrix.GeneralLinearGroup.map f x) := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm, ih]
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact hiter i δ

theorem normString_two (h2 : Module.finrank K L = 2) (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = δ * sigmaGL K L A σ δ := by
  unfold normString
  rw [h2]
  simp [List.range_succ]

theorem continuous_toTensorGL' [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] : Continuous (toTensorGL K L A) := by
  refine Continuous.units_map _ ?_
  have h : Continuous fun a : A => a • (1 : L ⊗[K] A) := continuous_id.fun_smul continuous_const
  have h' : Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
    refine h.congr fun a => ?_
    rw [← Algebra.algebraMap_eq_smul_one]
    rfl
  change Continuous fun M : Matrix (Fin 2) (Fin 2) A => M.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom)
  exact continuous_id.matrix_map h'

theorem forall_not_isSigmaConjugate_mul_scalar_iff (δ : GL (Fin 2) (L ⊗[K] A)) (ζ : (L ⊗[K] A)ˣ) :
    (∀ z : (L ⊗[K] A)ˣ, ¬ IsSigmaConjugate K L A σ (δ * sc ζ) (sc z)) ↔
      ∀ z : (L ⊗[K] A)ˣ, ¬ IsSigmaConjugate K L A σ δ (sc z) := by
  have key : ∀ (x : GL (Fin 2) (L ⊗[K] A)) (z : (L ⊗[K] A)ˣ),
      (sc z = x⁻¹ * (δ * sc ζ) * sigmaGL K L A σ x) ↔ (sc (z * ζ⁻¹) = x⁻¹ * δ * sigmaGL K L A σ x) := by
    intro x z
    have haux : x⁻¹ * (δ * sc ζ) * sigmaGL K L A σ x = (x⁻¹ * δ * sigmaGL K L A σ x) * sc ζ := by
      have h1 : sc ζ * sigmaGL K L A σ x = sigmaGL K L A σ x * sc ζ := scalar_mul_comm ζ _
      calc x⁻¹ * (δ * sc ζ) * sigmaGL K L A σ x = x⁻¹ * δ * (sc ζ * sigmaGL K L A σ x) := by group
        _ = x⁻¹ * δ * (sigmaGL K L A σ x * sc ζ) := by rw [h1]
        _ = _ := by group
    rw [haux, sc_mul, sc_inv]
    constructor
    · intro h
      rw [h]; group
    · intro h
      rw [← h]; group
  constructor
  · intro h z ⟨x, hx⟩
    refine h (z * ζ) ⟨x, ?_⟩
    rw [key, mul_inv_cancel_right]
    exact hx
  · intro h z ⟨x, hx⟩
    exact h (z * ζ⁻¹) ⟨x, (key x z).1 hx⟩

end Tensor

section Places

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Gad (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (AdeleRing (𝓞 K) K)

abbrev Garch (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (InfiniteAdeleRing K)

abbrev Gv (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : Type := GL (Fin 2) (v.adicCompletion K)

abbrev Gt (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)

abbrev Ht (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)

abbrev Gsl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  GL (Fin 2) (L ⊗[K] v.adicCompletion K)

def uArch (u : (AdeleRing (𝓞 K) K)ˣ) : (InfiniteAdeleRing K)ˣ :=
  Units.map (adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) u

def uAt (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) : (v.adicCompletion K)ˣ :=
  Units.map (((finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)) : AdeleRing (𝓞 K) K →* v.adicCompletion K) u

theorem glArch_centralScalar (u : (AdeleRing (𝓞 K) K)ˣ) :
    glArch (𝓞 K) K (centralScalar (𝓞 K) K u) = sc (uArch K u) :=
  map_scalar _ u

abbrev cpt (v : HeightOneSpectrum (𝓞 K)) (g : Gad K) : Gv K v := finComponent (𝓞 K) K v (glFin (𝓞 K) K g)

theorem cpt_centralScalar (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) :
    cpt K v (centralScalar (𝓞 K) K u) = sc (uAt K v u) := by
  rw [show cpt K v (centralScalar (𝓞 K) K u) =
      Matrix.GeneralLinearGroup.map ((finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)) (centralScalar (𝓞 K) K u)
    from rfl]
  exact map_scalar _ u

def zArch (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ :=
  Units.map ((tensorArchHom K L).toRingHom : L ⊗[K] AdeleRing (𝓞 K) K →* L ⊗[K] InfiniteAdeleRing K) ζ

def zAt (v : HeightOneSpectrum (𝓞 K)) (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : (L ⊗[K] v.adicCompletion K)ˣ :=
  Units.map ((tensorPlaceHom K L v).toRingHom : L ⊗[K] AdeleRing (𝓞 K) K →* L ⊗[K] v.adicCompletion K) ζ

theorem tensorArch_scalar (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : tensorArch K L (sc ζ) = sc (zArch K L ζ) :=
  map_scalar _ ζ

theorem tensorPlace_scalar (v : HeightOneSpectrum (𝓞 K)) (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    tensorPlace K L v (sc ζ) = sc (zAt K L v ζ) :=
  map_scalar _ ζ

theorem tensorArch_normString (σ : L ≃ₐ[K] L) (δ : Gt K L) :
    tensorArch K L (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (InfiniteAdeleRing K) σ (tensorArch K L δ) :=
  map_normString K L σ (AdeleRing (𝓞 K) K) (tensorArchHom K L).toRingHom (tensorArchHom_sigmaTensor K L σ) δ

theorem tensorPlace_normString (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (δ : Gt K L) :
    tensorPlace K L v (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (v.adicCompletion K) σ (tensorPlace K L v δ) :=
  map_normString K L σ (AdeleRing (𝓞 K) K) (tensorPlaceHom K L v).toRingHom (tensorPlaceHom_sigmaTensor K L σ v) δ

theorem tensorPlace_map_includeLeft (v : HeightOneSpectrum (𝓞 K)) (δ₀ : GL (Fin 2) L) :
    tensorPlace K L v (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀ := by
  show Matrix.GeneralLinearGroup.map (tensorPlaceHom K L v).toRingHom (Matrix.GeneralLinearGroup.map _ δ₀) = _
  rw [map_map_gl]
  refine map_congr_gl (fun l => ?_) δ₀
  show tensorPlaceHom K L v (l ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K)) = l ⊗ₜ[K] (1 : v.adicCompletion K)
  rw [tensorPlaceHom_tmul]
  rfl

theorem archEval_tensorArch_map_includeLeft (w : InfinitePlace K) (δ₀ : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.map (AlgHom.id K L)
          (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K => w.Completion) w)).toRingHom
        (tensorArch K L (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀)) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] w.Completion) δ₀ := by
  show Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map (tensorArchHom K L).toRingHom (Matrix.GeneralLinearGroup.map _ δ₀)) = _
  rw [map_map_gl, map_map_gl]
  refine map_congr_gl (fun l => ?_) δ₀
  show (Algebra.TensorProduct.map (AlgHom.id K L) (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K => w.Completion) w))
      (tensorArchHom K L (l ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K))) = l ⊗ₜ[K] (1 : w.Completion)
  rw [tensorArchHom_tmul]
  rfl

theorem nonempty_extension (v : HeightOneSpectrum (𝓞 K)) : Nonempty (v.Extension (𝓞 L)) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := Ideal.sum_ramification_inertia_extensions (𝓞 K) K L (𝓞 L) v
  simp at this
  exact Module.finrank_pos.ne' this.symm

theorem one_tmul_mem_semiLocalIntegers_iff (v : HeightOneSpectrum (𝓞 K)) (a : v.adicCompletion K) :
    (1 : L) ⊗ₜ[K] a ∈ semiLocalIntegers K L v ↔ a ∈ v.adicCompletionIntegers K := by
  constructor
  · intro h
    rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, semiLocalHomeomorph_eq] at h
    obtain ⟨w⟩ := nonempty_extension K L v
    have hw := h w (Set.mem_univ w)
    change (HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ((1 : L) ⊗ₜ[K] a)) w ∈
      (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) at hw
    rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul] at hw
    change HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w a ∈ w.1.adicCompletionIntegers L at hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom] at hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (pow_le_one_iff (HeightOneSpectrum.ramificationIdx_ne_zero (𝓞 K) (𝓞 L)
      (algebraMap_injective_of_field_isFractionRing (𝓞 K) (𝓞 L) K L) w.1)).1 hw
  · intro ha
    exact ⟨(1 : 𝓞 L) ⊗ₜ ⟨a, ha⟩, by rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, map_one]⟩

theorem toTensorGL_mem_semiLocalIntegralSet_iff (v : HeightOneSpectrum (𝓞 K)) (g : Gv K v) :
    toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v ↔ g ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet]
  show (∀ i j, ((toTensorGL K L (v.adicCompletion K) g : Gsl K L v) : Matrix (Fin 2) (Fin 2) _) i j ∈ semiLocalIntegers K L v) ∧
      (∀ i j, (((toTensorGL K L (v.adicCompletion K) g)⁻¹ : Gsl K L v) : Matrix (Fin 2) (Fin 2) _) i j ∈
        semiLocalIntegers K L v) ↔ _
  rw [← map_inv]
  simp only [coe_toTensorGL, Matrix.map_apply, one_tmul_mem_semiLocalIntegers_iff]

end Places

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
scoped instance instSecondCountableGad : SecondCountableTopology (Gad K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

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
scoped instance instT2SL (v : HeightOneSpectrum (𝓞 K)) : T2Space (L ⊗[K] v.adicCompletion K) := t2Space_tensor K L _
scoped instance instLocallyCompactSL (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (L ⊗[K] v.adicCompletion K) :=
  locallyCompactSpace_tensor K L _
scoped instance instLocallyCompactGsl (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gsl K L v) :=
  locallyCompactSpace_tensorGL K L _
scoped instance instIsTopologicalGroupGsl (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalGroup (Gsl K L v) :=
  isTopologicalGroup_tensorGL K L _
scoped instance instT2Gsl (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gsl K L v) := t2Space_tensorGL K L _
scoped instance instIsTopologicalRingTA : IsTopologicalRing (L ⊗[K] AdeleRing (𝓞 K) K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TA : T2Space (L ⊗[K] AdeleRing (𝓞 K) K) := t2Space_tensor K L _
scoped instance instLocallyCompactTA : LocallyCompactSpace (L ⊗[K] AdeleRing (𝓞 K) K) := locallyCompactSpace_tensor K L _
scoped instance instIsTopologicalGroupGt : IsTopologicalGroup (Gt K L) := isTopologicalGroup_tensorGL K L _
scoped instance instT2Gt : T2Space (Gt K L) := t2Space_tensorGL K L _
scoped instance instLocallyCompactGt : LocallyCompactSpace (Gt K L) := locallyCompactSpace_tensorGL K L _
scoped instance instIsTopologicalRingTI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TI : T2Space (L ⊗[K] InfiniteAdeleRing K) := t2Space_tensor K L _
scoped instance instLocallyCompactTI : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) := locallyCompactSpace_tensor K L _
scoped instance instIsTopologicalGroupHt : IsTopologicalGroup (Ht K L) := isTopologicalGroup_tensorGL K L _
scoped instance instLocallyCompactHt : LocallyCompactSpace (Ht K L) := locallyCompactSpace_tensorGL K L _
scoped instance instT2Ht : T2Space (Ht K L) := t2Space_tensorGL K L _

scoped instance instMeasurableSpaceGarch : MeasurableSpace (Garch K) := borel _
scoped instance instBorelSpaceGarch : BorelSpace (Garch K) := ⟨rfl⟩
scoped instance instMeasurableSpaceGv (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gv K v) := borel _
scoped instance instBorelSpaceGv (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gv K v) := ⟨rfl⟩
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
    (H : Subgroup (Gv K v)) : MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGv (v : HeightOneSpectrum (𝓞 K)) (H : Subgroup (Gv K v)) :
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

scoped instance instIsHaarLocalHaar (v : HeightOneSpectrum (𝓞 K)) : IsHaarMeasure (localHaar K v) := isHaarMeasure_localHaar K v
scoped instance instIsHaarArchHaarK : IsHaarMeasure (archHaarK K) := Measure.isHaarMeasure_haarMeasure _

theorem isClosed_twistedCentralizer (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := t2Space_tensorGL K L A
  have hcs : Continuous (sigmaGL K L A σ) := by
    refine Continuous.units_map _ ?_
    exact continuous_id.matrix_map (IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap)
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul hcs.inv
  have : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

scoped instance instLocallyCompactCentralizerGad (u : (AdeleRing (𝓞 K) K)ˣ) :
    LocallyCompactSpace (Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K))) := by
  have h : IsClosed ((Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)) : Set (Gad K))) := by
    rw [show centralScalar (𝓞 K) K u = sc u from rfl, centralizer_scalar_eq_top]
    exact isClosed_univ
  exact h.locallyCompactSpace
scoped instance instLocallyCompactCentralizerGarch (c : (InfiniteAdeleRing K)ˣ) :
    LocallyCompactSpace (Subgroup.centralizer ({sc c} : Set (Garch K))) := by
  have h : IsClosed ((Subgroup.centralizer ({sc c} : Set (Garch K))) : Set (Garch K)) := by
    rw [centralizer_scalar_eq_top]; exact isClosed_univ
  exact h.locallyCompactSpace
scoped instance instLocallyCompactCentralizerGv (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ) :
    LocallyCompactSpace (Subgroup.centralizer ({sc c} : Set (Gv K v))) := by
  have h : IsClosed ((Subgroup.centralizer ({sc c} : Set (Gv K v))) : Set (Gv K v)) := by
    rw [centralizer_scalar_eq_top]; exact isClosed_univ
  exact h.locallyCompactSpace
scoped instance instLocallyCompactTwistedGt (σ : L ≃ₐ[K] L) (δ : Gt K L) :
    LocallyCompactSpace (twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :=
  (isClosed_twistedCentralizer (K := K) (L := L) _ σ δ).locallyCompactSpace
scoped instance instLocallyCompactTwistedHt (σ : L ≃ₐ[K] L) (δ : Ht K L) :
    LocallyCompactSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ δ) :=
  (isClosed_twistedCentralizer (K := K) (L := L) _ σ δ).locallyCompactSpace
scoped instance instLocallyCompactTwistedGsl (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (δ : Gsl K L v) :
    LocallyCompactSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) :=
  (isClosed_twistedCentralizer (K := K) (L := L) _ σ δ).locallyCompactSpace

end Instances

section Transport

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def centralizerScalarEquiv {R : Type*} [CommRing R] [TopologicalSpace R] (c : Rˣ) :
    Subgroup.centralizer ({sc c} : Set (GL (Fin 2) R)) ≃ₜ* GL (Fin 2) R :=
  { (MulEquiv.subgroupCongr (centralizer_scalar_eq_top c)).trans Subgroup.topEquiv with
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk continuous_id }

def centralizerCsEquiv (u : (AdeleRing (𝓞 K) K)ˣ) :
    Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)) ≃ₜ* Gad K :=
  { (MulEquiv.subgroupCongr (centralizer_scalar_eq_top (R := AdeleRing (𝓞 K) K) u)).trans Subgroup.topEquiv with
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk continuous_id }

theorem orbitalIntegral_scalar_eq (μK : Measure (Gad K)) [μK.IsHaarMeasure] (u : (AdeleRing (𝓞 K) K)ˣ)
    (τ : Measure (Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)))) [τ.IsHaarMeasure]
    (f : Gad K → ℂ) (I : ℂ) (hI : IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μK (centralScalar (𝓞 K) K u) τ f I) :
    I = f (centralScalar (𝓞 K) K u) *
      (haarScalarFactor μK (Measure.map (centralizerCsEquiv u) τ) : ℝ) := by
  obtain ⟨w, ⟨hw0, hwm, hwc, hsec⟩, rfl⟩ := hI
  have hconj : ∀ x : Gad K, x⁻¹ * centralScalar (𝓞 K) K u * x = centralScalar (𝓞 K) K u := fun x =>
    conj_scalar (R := AdeleRing (𝓞 K) K) u x
  have hint : (fun x : Gad K => f (x⁻¹ * centralScalar (𝓞 K) K u * x) * ((w x : ℝ) : ℂ)) =
      fun x => f (centralScalar (𝓞 K) K u) * ((w x : ℝ) : ℂ) := funext fun x => by rw [hconj]
  show ∫ x, f (x⁻¹ * centralScalar (𝓞 K) K u * x) * ((w x : ℝ) : ℂ) ∂μK = _
  rw [hint, MeasureTheory.integral_const_mul]
  by_cases hf : f (centralScalar (𝓞 K) K u) = 0
  · rw [hf, zero_mul, zero_mul]
  congr 1
  set e := centralizerCsEquiv (K := K) u with he
  haveI : (Measure.map e τ).IsHaarMeasure := e.isHaarMeasure_map τ
  have hμ : μK = haarScalarFactor μK (Measure.map e τ) • Measure.map e τ := isMulLeftInvariant_eq_smul μK _
  have h1 : ∫ t : Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)), w ((t : Gad K) * 1) ∂τ = 1 :=
    hsec 1 (by rw [hconj]; exact hf)
  simp only [mul_one] at h1
  have h2 : ∫ x, ((w x : ℝ) : ℂ) ∂(Measure.map e τ) = 1 := by
    have hem : Measurable (fun t : Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)) => e t) :=
      e.continuous.measurable
    have hF : Measurable (fun x : Gad K => ((w x : ℝ) : ℂ)) := Complex.continuous_ofReal.measurable.comp hwm
    rw [MeasureTheory.integral_map hem.aemeasurable hF.aestronglyMeasurable]
    show ∫ t : Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)), ((w (t : Gad K) : ℝ) : ℂ) ∂τ = 1
    rw [integral_complex_ofReal, h1, Complex.ofReal_one]
  conv_lhs => rw [hμ]
  rw [integral_smul_nnreal_measure, h2, NNReal.smul_def, Complex.real_smul, mul_one]

theorem isOrbitalIntegralOn_arch_scalar (c : (InfiniteAdeleRing K)ˣ)
    (τ : Measure (Subgroup.centralizer ({sc c} : Set (Garch K)))) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (fa : Garch K → ℂ) :
    IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) (sc c) τ fa
      (fa (sc c) * (haarScalarFactor (archHaarK K) (Measure.map (centralizerScalarEquiv c) τ) : ℝ)) := by
  set e := centralizerScalarEquiv (R := InfiniteAdeleRing K) c with he
  set ν : Measure (Garch K) := Measure.map e τ with hν
  haveI hνH : ν.IsHaarMeasure := e.isHaarMeasure_map τ
  haveI hνR : ν.IsMulRightInvariant := by
    refine ⟨fun h => ?_⟩
    have hem : Measurable (e : _ → Garch K) := e.continuous.measurable
    rw [hν, Measure.map_map (measurable_mul_const h) hem]
    obtain ⟨g, rfl⟩ : ∃ g, e g = h := ⟨e.symm h, e.apply_symm_apply h⟩
    conv_rhs => rw [← map_mul_right_eq_self τ g]
    rw [Measure.map_map hem (measurable_mul_const g)]
    congr 1
  set gA : ℝ≥0 := haarScalarFactor (archHaarK K) ν with hgA
  have hHaar : archHaarK K = gA • ν := isMulLeftInvariant_eq_smul (archHaarK K) ν
  obtain ⟨k⟩ : Nonempty (PositiveCompacts (Garch K)) := inferInstance
  set A : Set (Garch K) := (k : Set (Garch K)) with hA
  have hAm : MeasurableSet A := k.isCompact.measurableSet
  have hApos : ν.real A ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(measure_pos_of_nonempty_interior ν k.interior_nonempty).ne', k.isCompact.measure_lt_top.ne⟩
  set m : ℝ := ν.real A with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  set w : Garch K → ℝ := A.indicator fun _ => m⁻¹ with hw
  have hsec : IsSectionFnOn (InfiniteAdeleRing K) (sc c) τ fa w := by
    refine ⟨fun x => Set.indicator_nonneg (fun _ _ => inv_nonneg.2 hm0) x, measurable_const.indicator hAm,
      HasCompactSupport.intro k.isCompact fun x hx => Set.indicator_of_notMem hx _, fun x _ => ?_⟩
    have hem : Measurable (e : _ → Garch K) := e.continuous.measurable
    have hF : Measurable (fun g : Garch K => w (g * x)) := (measurable_const.indicator hAm).comp (measurable_mul_const x)
    calc ∫ s : Subgroup.centralizer ({sc c} : Set (Garch K)), w ((s : Garch K) * x) ∂τ
        = ∫ s : Subgroup.centralizer ({sc c} : Set (Garch K)), w (e s * x) ∂τ := by rfl
      _ = ∫ g, w (g * x) ∂ν := by
          rw [hν, MeasureTheory.integral_map hem.aemeasurable hF.aestronglyMeasurable]
      _ = ∫ g, ((fun g => g * x) ⁻¹' A).indicator (fun _ => m⁻¹) g ∂ν := by congr 1
      _ = ν.real ((fun g => g * x) ⁻¹' A) • m⁻¹ := integral_indicator_const _ (hAm.preimage (measurable_mul_const x))
      _ = ν.real A • m⁻¹ := by
          rw [measureReal_def, measureReal_def, ← Measure.map_apply (measurable_mul_const x) hAm, map_mul_right_eq_self]
      _ = 1 := by rw [smul_eq_mul, ← hm, mul_inv_cancel₀ hApos]
  refine ⟨w, hsec, ?_⟩
  have h1 : (fun x => fa (x⁻¹ * sc c * x) * (w x : ℂ)) = fun x => A.indicator (fun _ => (m⁻¹ : ℂ) * fa (sc c)) x := by
    funext x
    rw [conj_scalar]
    by_cases hx : x ∈ A
    · simp [hw, hx, mul_comm]
    · simp [hw, hx]
  rw [h1, integral_indicator_const _ hAm]
  rw [show (archHaarK K).real A = (gA : ℝ) * m by
    rw [hm, measureReal_def, measureReal_def, hHaar, Measure.smul_apply, ENNReal.toReal_smul, NNReal.smul_def, smul_eq_mul]]
  rw [Complex.real_smul]
  have hm0' : (m : ℂ) ≠ 0 := by exact_mod_cast hApos
  push_cast
  field_simp

end Transport

section LocalTorus

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (δ : Gsl K L v)

def unitTwistedCompacts : PositiveCompacts (twistedCentralizer K L (v.adicCompletion K) σ δ) where
  carrier := Subtype.val ⁻¹' semiLocalIntegralSet K L v
  isCompact' := (IsClosedEmbedding.subtypeVal (isClosed_twistedCentralizer (K := K) (L := L) _ σ δ)).isCompact_preimage
    (isCompact_semiLocalIntegralSet K L v)
  interior_nonempty' := by
    rw [((isOpen_semiLocalIntegralSet K L v).preimage continuous_subtype_val).interior_eq]
    exact ⟨1, one_mem_semiLocalIntegralSet K L v⟩

def unitTwistedHaar : Measure (twistedCentralizer K L (v.adicCompletion K) σ δ) :=
  Measure.haarMeasure (unitTwistedCompacts σ v δ)

scoped instance isHaarMeasure_unitTwistedHaar : (unitTwistedHaar σ v δ).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

theorem unitTwistedHaar_self : unitTwistedHaar σ v δ (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1 :=
  Measure.haarMeasure_self

end LocalTorus

section Main

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Tu (u : (AdeleRing (𝓞 K) K)ˣ) : Subgroup (Gad K) :=
  Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K))
abbrev Tua (u : (AdeleRing (𝓞 K) K)ˣ) : Subgroup (Garch K) := Subgroup.centralizer ({sc (uArch K u)} : Set (Garch K))
abbrev Tuv (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gv K v) :=
  Subgroup.centralizer ({sc (uAt K v u)} : Set (Gv K v))

abbrev dd (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : Gt K L :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * sc c
abbrev Td (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : Subgroup (Gt K L) :=
  twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (dd δ₀ c)
abbrev Tda (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : Subgroup (Ht K L) :=
  twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L (dd δ₀ c))
abbrev Tdv (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (Gsl K L v) :=
  twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v (dd δ₀ c))

abbrev unitShell (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Set (Tdv σ δ₀ c v) :=
  {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
      Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
        Units.map (Algebra.TensorProduct.includeRight :
          v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}

def HFin (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (τM : Measure (Gv K v)) (τM' : Measure (Tdv σ δ₀ c v)) : Prop :=
  (∃ y : Gsl K L v,
      IsNormConjugator K L (v.adicCompletion K) σ (cpt K v (centralScalar (𝓞 K) K u)) (tensorPlace K L v (dd δ₀ c)) y ∧
      Measure.map (fun t : Tdv σ δ₀ c v => y⁻¹ * (t : Gsl K L v) * y) τM' =
        Measure.map (toTensorGL K L (v.adicCompletion K)) τM) ∨
  ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ IsSigmaConjugate K L (v.adicCompletion K) σ (tensorPlace K L v (dd δ₀ c)) (sc z)) ∧
    τM' (unitShell σ δ₀ c v) * (Ideal.absNorm v.asIdeal : ENNReal) = τM (localIntegralSet K v) + τM' (unitShell σ δ₀ c v))

set_option maxHeartbeats 16000000 in

theorem main
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (μK : Measure (Gad K)) [hμK : μK.IsHaarMeasure]
    (μL : Measure (Gt K L)) [hμL : μL.IsHaarMeasure]
    (cK cL : ℝ) (hcK : 0 < cK) (hcL : 0 < cL)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : Gad K → ℂ) (fa : Garch K → ℂ) (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv K v → ℂ),
        AEStronglyMeasurable fa (archHaarK K) →
        (∀ v ∈ S, AEStronglyMeasurable (fS v) (localHaar K v)) →
        (∀ g : Gad K, (∀ v ∉ S, cpt K v g ∈ localIntegralSet K v) → f g = fa (glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (cpt K v g)) →
        (∀ g : Gad K, (∃ v ∉ S, cpt K v g ∉ localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂μK = cK * (∫ x, fa x ∂(archHaarK K)) * ∏ v ∈ S, ∫ y, fS v y ∂(localHaar K v))
    (hG' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (F : Gt K L → ℂ) (Fa : Ht K L → ℂ) (FS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
        AEStronglyMeasurable Fa (archHaarL K L) →
        (∀ v ∈ S, AEStronglyMeasurable (FS v) (semiLocalHaar K L v)) →
        (∀ x : Gt K L, (∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) →
            F x = Fa (tensorArch K L x) * ∏ v ∈ S, FS v (tensorPlace K L v x)) →
        (∀ x : Gt K L, (∃ v ∉ S, tensorPlace K L v x ∉ semiLocalIntegralSet K L v) → F x = 0) →
          ∫ x, F x ∂μL = cL * (∫ y, Fa y ∂(archHaarL K L)) * ∏ v ∈ S, ∫ y, FS v y ∂(semiLocalHaar K L v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : Gad K → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ)
    (fa : Garch K → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv K v → ℂ)
    (hφ : IsSemiLocalFactorization K L S φ φa φf φS)
    (hf : IsUnitFactorization K S f fa ff fS)
    (hArch : AreMatchingArch K L σ φa fa)
    (hLoc : ∀ v ∈ S, AreMatchingLocal K L v σ (φS v) (fS v))
    (hunit : ∀ v ∉ S, AreMatchingLocal K L v σ
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
      ((localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : normString K L (AdeleRing (𝓞 K) K) σ (dd δ₀ c) = toTensorGL K L (AdeleRing (𝓞 K) K) (centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ), x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠ sc z)
    (τ : Measure (Tu u)) [hτ : τ.IsHaarMeasure]
    (τ' : Measure (Td σ δ₀ c)) [hτ' : τ'.IsHaarMeasure]
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hD' : ∀ D' : Set (Td σ δ₀ c),
      IsFundamentalDomain
        (((sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf (Td σ δ₀ c)).op D' τ' →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
          C * ENNReal.ofReal (Real.log (b / a)))
    (hD : ∀ D : Set (Tu u),
      IsFundamentalDomain (((globalPoints (𝓞 K) K).range).subgroupOf (Tu u)).op D τ →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (t : Gad K)) ∈ Set.Icc a b}) =
          (Module.finrank K L : ENNReal) * C * ENNReal.ofReal (Real.log (b / a)))
    (I I' : ℂ)
    (hI' : IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μL (dd δ₀ c) τ' (φ ∘ baseChangeGL K L) I')
    (hI : IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μK (centralScalar (𝓞 K) K u) τ f I) :
    (cK : ℂ) * I' = cL * I := by
  classical
  set δ : Gt K L := dd δ₀ c with hδ_def

  have hprime : (Module.finrank K L).Prime := by rw [h2]; exact Nat.prime_two
  obtain ⟨hgal, hord, hzp⟩ := AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hprime σ hσ
  haveI := hgal
  have hgen : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ := fun θ => hzp ▸ Subgroup.mem_top θ

  set e := centralizerCsEquiv (K := K) u with he_def
  set ea := centralizerScalarEquiv (R := InfiniteAdeleRing K) (uArch K u) with hea_def
  set ev := fun v : HeightOneSpectrum (𝓞 K) => centralizerScalarEquiv (R := v.adicCompletion K) (uAt K v u) with hev_def
  have hme : Measurable (e : Tu u → Gad K) := e.continuous.measurable
  have hmes : Measurable (e.symm : Gad K → Tu u) := e.symm.continuous.measurable
  have hmea : Measurable (ea : Tua u → Garch K) := ea.continuous.measurable
  have hmeas : Measurable (ea.symm : Garch K → Tua u) := ea.symm.continuous.measurable
  have hmev : ∀ v, Measurable ((ev v) : Tuv u v → Gv K v) := fun v => (ev v).continuous.measurable
  have hmevs : ∀ v, Measurable ((ev v).symm : Gv K v → Tuv u v) := fun v => (ev v).symm.continuous.measurable

  have hya : IsNormConjugator K L (InfiniteAdeleRing K) σ (sc (uArch K u)) (tensorArch K L δ) 1 := by
    unfold IsNormConjugator
    rw [inv_one, one_mul, mul_one, ← tensorArch_normString, hN, tensorArch_toTensorGL, glArch_centralScalar]
  have hyv : ∀ v : HeightOneSpectrum (𝓞 K), IsNormConjugator K L (v.adicCompletion K) σ (sc (uAt K v u))
      (tensorPlace K L v δ) 1 := by
    intro v
    unfold IsNormConjugator
    rw [inv_one, one_mul, mul_one, ← tensorPlace_normString, hN, tensorPlace_toTensorGL]
    exact congrArg _ (cpt_centralScalar K v u).symm

  have hδ₀c : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ ∈ Subgroup.center (GL (Fin 2) L) := by
    set D : Gt K L := Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ with hD
    have hN2 : (D * sc c) * sigmaGL K L _ σ (D * sc c) = toTensorGL K L _ (centralScalar (𝓞 K) K u) := by
      rw [← normString_two K L σ _ h2]; exact hN
    rw [map_mul, sigmaGL_map_includeLeft] at hN2

    have hsc : sigmaGL K L (AdeleRing (𝓞 K) K) σ (sc c) =
        sc (Units.map (sigmaTensor K L (AdeleRing (𝓞 K) K) σ : L ⊗[K] AdeleRing (𝓞 K) K →* L ⊗[K] AdeleRing (𝓞 K) K) c) :=
      map_scalar _ c
    rw [hsc, show toTensorGL K L _ (centralScalar (𝓞 K) K u) = toTensorGL K L _ (sc u) from rfl, toTensorGL_scalar] at hN2
    set c' := Units.map (sigmaTensor K L (AdeleRing (𝓞 K) K) σ : L ⊗[K] AdeleRing (𝓞 K) K →* L ⊗[K] AdeleRing (𝓞 K) K) c with hc'
    set u' := Units.map ((Algebra.TensorProduct.includeRight : AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K).toRingHom :
      AdeleRing (𝓞 K) K →* L ⊗[K] AdeleRing (𝓞 K) K) u with hu'
    set Dσ : Gt K L := Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K)
      (Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀) with hDσ

    have hDD : D * Dσ = sc (u' * (c * c')⁻¹) := by
      have h1 : D * sc c * (Dσ * sc c') = D * Dσ * sc (c * c') := by
        rw [sc_mul, mul_assoc D (sc c), ← mul_assoc (sc c) Dσ, scalar_mul_comm c Dσ]; group
      rw [h1] at hN2
      rw [sc_mul, sc_inv, ← hN2]; group

    have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) :
        GL (Fin 2) L → Gt K L) := by
      intro x y hxy
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      have h := congrArg (fun g : Gt K L => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) i j) hxy
      have hinjL : Function.Injective (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) := by
        haveI : Nontrivial (AdeleRing (𝓞 K) K) := inferInstanceAs (Nontrivial (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
        exact Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K (AdeleRing (𝓞 K) K)).injective
      exact hinjL h
    rw [Subgroup.mem_center_iff]
    intro g
    apply hinj
    have hz : Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K)
        (δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀) = sc (u' * (c * c')⁻¹) := by
      rw [map_mul]; exact hDD
    rw [map_mul _ g, map_mul _ (δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀) g, hz]
    exact (scalar_mul_comm _ _).symm

  set P : HeightOneSpectrum (𝓞 K) → Prop := fun v =>
    ∀ z : (L ⊗[K] v.adicCompletion K)ˣ, ¬ IsSigmaConjugate K L (v.adicCompletion K) σ (tensorPlace K L v δ) (sc z) with hP_def
  have hPiff : ∀ v, P v ↔ ∀ z : (L ⊗[K] v.adicCompletion K)ˣ, ¬ IsSigmaConjugate K L (v.adicCompletion K) σ
      (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀) (sc z) := by
    intro v
    simp only [hP_def]
    rw [show tensorPlace K L v δ = Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀ *
        sc (zAt K L v c) by rw [hδ_def, map_mul, tensorPlace_map_includeLeft, tensorPlace_scalar]]
    exact forall_not_isSigmaConjugate_mul_scalar_iff K L σ _ _ _
  have hQiff : ∀ w : InfinitePlace K,
      (∀ z : (L ⊗[K] w.Completion)ˣ, ¬ IsSigmaConjugate K L w.Completion σ
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.map (AlgHom.id K L)
          (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K => w.Completion) w)).toRingHom (tensorArch K L δ)) (sc z)) ↔
      ∀ z : (L ⊗[K] w.Completion)ˣ, ¬ IsSigmaConjugate K L w.Completion σ
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] w.Completion) δ₀) (sc z) := by
    intro w
    have hcomp : ∃ ζ : (L ⊗[K] w.Completion)ˣ, Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.map (AlgHom.id K L)
          (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K => w.Completion) w)).toRingHom (tensorArch K L δ) =
        Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] w.Completion) δ₀ * sc ζ :=
      by
        refine ⟨Units.map ((Algebra.TensorProduct.map (AlgHom.id K L)
            (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K => w.Completion) w)).toRingHom.toMonoidHom) (zArch K L c), ?_⟩
        rw [hδ_def, map_mul]
        erw [map_mul]
        rw [archEval_tensorArch_map_includeLeft, tensorArch_scalar]
        erw [map_scalar]
        rfl
    obtain ⟨ζ, hζ⟩ := hcomp
    rw [hζ]
    exact forall_not_isSigmaConjugate_mul_scalar_iff K L σ _ _ _

  have hτ'r : τ'.IsMulRightInvariant :=
    AutomorphicForm.isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
      K L h2 σ hgen δ u hN τ' hτ'

  letI mM : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
  haveI : BorelSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := ⟨rfl⟩
  obtain ⟨τc, τa', hτcH, hτa'H, hτcR, hτa'R, n₁, n₂, e₁, e₂, s, hs0, hstop, hli1, hsp1, hli2, hsp2, hgram1, hgram2⟩ :=
    AutomorphicForm.exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two
      K L h2 σ hgen (sc (uArch K u)) ⟨_, rfl⟩ (tensorArch K L δ) 1 hya
  haveI := hτcH
  haveI := hτa'H
  haveI := hτcR
  set gA : ℝ≥0 := haarScalarFactor (archHaarK K) (Measure.map ea τc) with hgA_def
  haveI hνaH : (Measure.map ea τc).IsHaarMeasure := ea.isHaarMeasure_map τc
  have hgA0 : 0 < gA := haarScalarFactor_pos_of_isHaarMeasure _ _
  have harchHaar : archHaarK K = gA • Measure.map ea τc := isMulLeftInvariant_eq_smul _ _

  set τu : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tdv σ δ₀ c v) := fun v => unitTwistedHaar σ v (tensorPlace K L v δ) with hτu_def
  have hτuH : ∀ v, (τu v).IsHaarMeasure := fun v => isHaarMeasure_unitTwistedHaar σ v _
  have hτu1 : ∀ v : HeightOneSpectrum (𝓞 K), τu v (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1 := fun v =>
    unitTwistedHaar_self σ v _
  obtain ⟨cT, hcT, hT⟩ := AutomorphicForm.exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
    K L σ δ τ' hτ' τa' hτa'H τu hτuH hτu1

  have hE := AutomorphicForm.exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant
    K L σ μL hμL (archHaarL K L) cL hG' δ τ' hτ' hτ'r τa' hτa'H τu hτuH hτu1 cT hcT hT S φ φa φf φS hφ I' hI'

  obtain ⟨hφa, -, hφS, -, -, -⟩ := hφ
  obtain ⟨hfa, -, hfS, hprod, hzero, hfac⟩ := hf

  set τKv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tuv u v) := fun v => Measure.map (ev v).symm (localHaar K v)
    with hτKv_def
  have hτKvH : ∀ v, (τKv v).IsHaarMeasure := fun v => (ev v).symm.isHaarMeasure_map _
  have hτKv_int : ∀ v, τKv v {t | (t : Gv K v) ∈ localIntegralSet K v} = 1 := by
    intro v
    show Measure.map (ev v).symm (localHaar K v) (Subtype.val ⁻¹' localIntegralSet K v) = 1
    rw [Measure.map_apply (hmevs v) ((isOpen_localIntegralSet K v).measurableSet.preimage continuous_subtype_val.measurable)]
    exact localHaar_localIntegralSet K v

  set φv : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ := fun v =>
    if v ∈ S then φS v else (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ) with hφv_def
  set fv : ∀ v : HeightOneSpectrum (𝓞 K), Gv K v → ℂ := fun v =>
    if v ∈ S then fS v else (localIntegralSet K v).indicator fun _ => (1 : ℂ) with hfv_def
  have hmv : ∀ v, AreMatchingLocal K L v σ (φv v) (fv v) := by
    intro v
    by_cases hv : v ∈ S
    · simp only [hφv_def, hfv_def, hv, if_true]; exact hLoc v hv
    · simp only [hφv_def, hfv_def, hv, if_false]; exact hunit v hv
  have hφvt : ∀ v, IsSemiLocalTestFn K L v (φv v) := by
    intro v
    by_cases hv : v ∈ S
    · simp only [hφv_def, hv, if_true]; exact hφS v hv
    · simp only [hφv_def, hv, if_false]; exact isSemiLocalTestFn_indicator_semiLocalIntegralSet K L v
  have hfvt : ∀ v, IsLocalTestFn K v (fv v) := by
    intro v
    by_cases hv : v ∈ S
    · simp only [hfv_def, hv, if_true]; exact hfS v hv
    · simp only [hfv_def, hv, if_false]; exact isLocalTestFn_indicator_localIntegralSet K v

  set ε : HeightOneSpectrum (𝓞 K) → ℂ := fun v => if P v then -1 else 1 with hε_def

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ (τM : Measure (Gv K v)) (τM' : Measure (Tdv σ δ₀ c v)) (α β : ℝ≥0),
      τM.IsHaarMeasure ∧ τM'.IsHaarMeasure ∧ α ≠ 0 ∧ β ≠ 0 ∧ localHaar K v = α • τM ∧ τu v = β • τM' ∧
      HFin σ δ₀ c u v τM τM' ∧ (¬ P v → β = 1) ∧
      ∀ J : ℂ, IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τu v) (φv v) J →
        J = ε v * fv v (sc (uAt K v u)) * (α : ℂ) * ((β⁻¹ : ℝ≥0) : ℂ) := by
    intro v

    have hδv : normString K L (v.adicCompletion K) σ (tensorPlace K L v δ) = toTensorGL K L (v.adicCompletion K) (sc (uAt K v u)) := by
      rw [← tensorPlace_normString, hN, tensorPlace_toTensorGL]
      exact congrArg _ (cpt_centralScalar K v u)

    obtain ⟨τM, τM', α, β, hτMH, hτM'H, hα0, hβ0, hHaarα, hτuβ, hcompat, hβ1, hvalJ⟩ :=
      AutomorphicForm.exists_isHaarMeasure_and_isTwistedOrbitalIntegral_eq_mul_apply_scalar_of_normString_eq_toTensorGL_scalar_of_finrank_eq_two
        K L h2 σ hσ v (uAt K v u) (tensorPlace K L v δ) hδv (τu v) (hτuH v) (φv v) (hφvt v) (fv v) (hfvt v) (hmv v)
    refine ⟨τM, τM', α, β, hτMH, hτM'H, hα0, hβ0, hHaarα, hτuβ, ?_, fun hnP => hβ1 ?_, fun J hJ => ?_⟩
    · rcases hcompat with ⟨y, hy, hcpl⟩ | ⟨hP, hrule⟩
      · left
        refine ⟨y, ?_, hcpl⟩
        unfold IsNormConjugator at hy
        show toTensorGL K L (v.adicCompletion K) (cpt K v (centralScalar (𝓞 K) K u)) = _
        rw [cpt_centralScalar]; exact hy
      · right; exact ⟨hP, hrule⟩
    · by_contra h
      push Not at h
      exact hnP h
    · obtain ⟨h1, h2'⟩ := hvalJ J hJ
      by_cases hPv : P v
      · rw [h1 hPv]; simp only [hε_def, hPv, if_true]; ring
      · have hz : ∃ z : (L ⊗[K] v.adicCompletion K)ˣ, IsSigmaConjugate K L (v.adicCompletion K) σ (tensorPlace K L v δ) (sc z) := by
          by_contra h; push Not at h; exact hPv h
        rw [h2' hz]; simp only [hε_def, hPv, if_false]; ring
  choose τM τM' α β hτMH hτM'H hα0 hβ0 hHaarα hτuβ hHFin hβ1 hval using hloc

  set rexp : ℕ := Nat.card {w : NumberField.InfinitePlace K //
      ∀ z : (L ⊗[K] w.Completion)ˣ, ¬ IsSigmaConjugate K L w.Completion σ
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.map (AlgHom.id K L)
          (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K => w.Completion) w)).toRingHom (tensorArch K L δ))
        (sc z)} with hrexp_def
  have harch : ∀ J : ℂ, IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L)
      (tensorArch K L δ) τa' (φa ∘ archIdentGL K L) J → J = (-1 : ℂ) ^ rexp * (fa (sc (uArch K u)) * (gA : ℂ)) := by
    intro J hJ
    have h := AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two
      K L h2 σ hgen (sc (uArch K u)) ⟨_, rfl⟩ (tensorArch K L δ) 1 hya τc hτcH τa' hτa'H
      ⟨n₁, n₂, e₁, e₂, s, hs0, hstop, hli1, hsp1, hli2, hsp2, hgram1, hgram2⟩ φa hφa fa hfa hArch
      (fa (sc (uArch K u)) * (gA : ℝ)) J hJ (isOrbitalIntegralOn_arch_scalar (uArch K u) τc fa)
    rw [h]

  set ν₀ : Measure (Gad K) := Measure.map e τ with hν₀_def
  haveI hν₀H : ν₀.IsHaarMeasure := e.isHaarMeasure_map τ
  set r₀ : ℝ≥0 := haarScalarFactor ν₀ μK with hr₀_def
  have hr₀0 : 0 < r₀ := haarScalarFactor_pos_of_isHaarMeasure ν₀ μK
  have hν₀ : ν₀ = r₀ • μK := isMulLeftInvariant_eq_smul ν₀ μK
  have hIval : I = f (centralScalar (𝓞 K) K u) * ((r₀⁻¹ : ℝ≥0) : ℝ) := by
    rw [orbitalIntegral_scalar_eq μK u τ f I hI]
    congr 2
    have hmul := haarScalarFactor_eq_mul μK ν₀ μK
    rw [haarScalarFactor_self] at hmul
    show ((haarScalarFactor μK ν₀ : ℝ≥0) : ℝ) = ((r₀⁻¹ : ℝ≥0) : ℝ)
    rw [eq_inv_of_mul_eq_one_left hmul.symm]

  have hfu : f (centralScalar (𝓞 K) K u) = fa (sc (uArch K u)) * ff (glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) := by
    rw [hfac, glArch_centralScalar]

  have hkill_v : ∀ v, fv v (sc (uAt K v u)) = 0 → f (centralScalar (𝓞 K) K u) = 0 := by
    intro v hv0
    rw [hfu]
    by_cases hint : ∀ w ∉ S, cpt K w (centralScalar (𝓞 K) K u) ∈ localIntegralSet K w
    · by_cases hvS : v ∈ S
      · rw [hprod _ hint, Finset.prod_eq_zero hvS (by
          simp only [hfv_def, hvS, if_true] at hv0; rw [← cpt_centralScalar] at hv0; exact hv0), mul_zero]
      · simp only [hfv_def, hvS, if_false] at hv0
        have hmem := hint v hvS
        rw [cpt_centralScalar] at hmem
        rw [Set.indicator_of_mem hmem] at hv0
        exact absurd hv0 one_ne_zero
    · push Not at hint
      obtain ⟨w, hw, hw'⟩ := hint
      rw [hzero _ ⟨w, hw, hw'⟩, mul_zero]
  have hkill_a : fa (sc (uArch K u)) = 0 → f (centralScalar (𝓞 K) K u) = 0 := fun h0 => by rw [hfu, h0, zero_mul]
  have hgA0' : ((gA : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hgA0.ne'
  have hαβ0 : ∀ v, (α v : ℂ) * (((β v)⁻¹ : ℝ≥0) : ℂ) ≠ 0 := by
    intro v
    have h1 : ((α v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hα0 v
    have h2' : ((((β v)⁻¹ : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero (hβ0 v)
    exact_mod_cast mul_ne_zero h1 h2'
  have hε0 : ∀ v, ε v ≠ 0 := by
    intro v; simp only [hε_def]; split_ifs <;> norm_num

  have hIv0 : ∀ v J, IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τu v) (φv v) J → J = 0 →
      f (centralScalar (𝓞 K) K u) = 0 := by
    intro v J hJ hJ0
    have h := hval v J hJ
    rw [hJ0] at h
    have : fv v (sc (uAt K v u)) = 0 := by
      have h' : ε v * fv v (sc (uAt K v u)) * ((α v : ℂ) * (((β v)⁻¹ : ℝ≥0) : ℂ)) = 0 := by rw [← mul_assoc]; exact h.symm
      rcases mul_eq_zero.1 h' with h'' | h''
      · rcases mul_eq_zero.1 h'' with h3 | h3
        · exact absurd h3 (hε0 v)
        · exact h3
      · exact absurd h'' (hαβ0 v)
    exact hkill_v v this

  rcases hE with ⟨hI'0, hobs⟩ | ⟨S₁, hSS₁, Ia, Iv, hIa, hIvS, hIvnS, hprodT⟩
  ·
    rw [hI'0, mul_zero, hIval]
    suffices h0 : f (centralScalar (𝓞 K) K u) = 0 by rw [h0, zero_mul, mul_zero]
    rcases hobs with harch0 | ⟨v, hvS, hv0⟩ | ⟨v, hvS, hv0⟩
    ·
      have h0 : IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) (tensorArch K L δ) τa'
          (φa ∘ archIdentGL K L) 0 :=
        ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun x hx => absurd (harch0 x) hx⟩, by simp⟩
      have := harch 0 h0
      apply hkill_a
      have h' : (-1 : ℂ) ^ rexp * (fa (sc (uArch K u)) * (gA : ℂ)) = 0 := this.symm
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact absurd h'' (pow_ne_zero _ (by norm_num))
      · rcases mul_eq_zero.1 h'' with h3 | h3
        · exact h3
        · exact absurd h3 hgA0'
    ·
      have h0 : IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τu v) (φv v) 0 := by
        refine ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun x hx => ?_⟩, by simp⟩
        simp only [hφv_def, hvS, if_true] at hx
        exact absurd (hv0 x) hx
      exact hIv0 v 0 h0 rfl
    ·
      have h0 : IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τu v) (φv v) 0 := by
        refine ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun x hx => ?_⟩, by simp⟩
        simp only [hφv_def, hvS, if_false] at hx
        exact absurd (Set.indicator_of_notMem (hv0 x) _) hx
      exact hIv0 v 0 h0 rfl
  ·

    have hIvTOI : ∀ v, IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τu v) (φv v) (Iv v) := by
      intro v
      by_cases hv : v ∈ S
      · have h := hIvS v hv
        have : φS v = φv v := by simp only [hφv_def, hv, if_true]
        rw [this] at h; exact h
      · have h := hIvnS v hv
        have : ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) = φv v := by simp only [hφv_def, hv, if_false]
        rw [this] at h; exact h
    have hIvval : ∀ v, Iv v = ε v * fv v (sc (uAt K v u)) * (α v : ℂ) * (((β v)⁻¹ : ℝ≥0) : ℂ) := fun v =>
      hval v (Iv v) (hIvTOI v)
    have hIaval : Ia = (-1 : ℂ) ^ rexp * (fa (sc (uArch K u)) * (gA : ℂ)) := harch Ia hIa
    have hI'S₁ := hprodT S₁ (Finset.Subset.refl _)
    by_cases hI'0 : I' = 0
    ·
      rw [hI'0, mul_zero, hIval]
      suffices h0 : f (centralScalar (𝓞 K) K u) = 0 by rw [h0, zero_mul, mul_zero]
      rw [hI'0] at hI'S₁
      have h' : (cL : ℂ) * ((cT⁻¹ : ℝ) : ℂ) * Ia * ∏ v ∈ S₁, Iv v = 0 := hI'S₁.symm
      have hcL0 : (cL : ℂ) ≠ 0 := by exact_mod_cast hcL.ne'
      have hcT0 : ((cT⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero hcT.ne'
      rcases mul_eq_zero.1 h' with h'' | h''
      · rcases mul_eq_zero.1 h'' with h3 | h3
        · exact absurd h3 (mul_ne_zero hcL0 hcT0)
        ·
          rw [hIaval] at h3
          apply hkill_a
          rcases mul_eq_zero.1 h3 with h4 | h4
          · exact absurd h4 (pow_ne_zero _ (by norm_num))
          · rcases mul_eq_zero.1 h4 with h5 | h5
            · exact h5
            · exact absurd h5 hgA0'
      · obtain ⟨v, -, hv⟩ := Finset.prod_eq_zero_iff.1 h''
        exact hIv0 v (Iv v) (hIvTOI v) hv
    ·

      have hIv1 : ∀ v ∉ S₁, Iv v = 1 := by
        intro v hv
        have h := hprodT (insert v S₁) (Finset.subset_insert v S₁)
        rw [Finset.prod_insert hv] at h
        have h' : I' = Iv v * I' := by
          conv_rhs => rw [hI'S₁]
          rw [h]; ring
        have h'' : Iv v * I' = 1 * I' := by rw [one_mul]; exact h'.symm
        exact mul_right_cancel₀ hI'0 h''

      have hout : ∀ v ∉ S₁, ¬ P v ∧ α v = 1 ∧ β v = 1 ∧ cpt K v (centralScalar (𝓞 K) K u) ∈ localIntegralSet K v := by
        intro v hv
        have hvS : v ∉ S := fun h => hv (hSS₁ h)
        have h1 := hIv1 v hv
        rw [hIvval v] at h1
        simp only [hfv_def, hvS, if_false] at h1

        have hmem : sc (uAt K v u) ∈ localIntegralSet K v := by
          by_contra hn
          rw [Set.indicator_of_notMem hn, mul_zero, zero_mul, zero_mul] at h1
          exact zero_ne_one h1
        rw [Set.indicator_of_mem hmem, mul_one] at h1

        have hnotP : ¬ P v := by
          intro hPv
          simp only [hε_def, hPv, if_true] at h1
          have hre : ((-1 : ℂ) * (α v : ℂ) * (((β v)⁻¹ : ℝ≥0) : ℂ)).re = (1 : ℂ).re := by rw [h1]
          have : ((-1 : ℂ) * (α v : ℂ) * (((β v)⁻¹ : ℝ≥0) : ℂ)).re = -((α v : ℝ) * ((β v)⁻¹ : ℝ≥0)) := by
            have e1 : ((-1 : ℂ) * (α v : ℂ) * (((β v)⁻¹ : ℝ≥0) : ℂ)) = (((-((α v : ℝ) * ((β v)⁻¹ : ℝ≥0)) : ℝ)) : ℂ) := by push_cast; ring
            rw [e1, Complex.ofReal_re]
          rw [this, Complex.one_re] at hre
          have hpos : 0 ≤ (α v : ℝ) * ((β v)⁻¹ : ℝ≥0) := by positivity
          linarith
        have hβv : β v = 1 := hβ1 v hnotP
        simp only [hε_def, hnotP, if_false, one_mul, hβv, inv_one, NNReal.coe_one, Complex.ofReal_one, mul_one] at h1
        have hαv : α v = 1 := by exact_mod_cast h1
        refine ⟨hnotP, hαv, hβv, ?_⟩
        rw [cpt_centralScalar]; exact hmem

      set sgn : ℂ := ∏ v ∈ S₁, ε v with hsgn_def
      have hsgn : sgn = (-1 : ℂ) ^ (S₁.filter P).card := by
        rw [hsgn_def, hε_def, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

      set κ : ℂ := ∏ v ∈ S₁, ((α v : ℂ) * (((β v)⁻¹ : ℝ≥0) : ℂ)) with hκ_def
      have hprodS₁ : ∏ v ∈ S₁, Iv v = sgn * κ * ff (glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) := by
        have h1 : ∏ v ∈ S₁, Iv v = (∏ v ∈ S₁, ε v) * (∏ v ∈ S₁, ((α v : ℂ) * (((β v)⁻¹ : ℝ≥0) : ℂ))) *
            ∏ v ∈ S₁, fv v (sc (uAt K v u)) := by
          rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun v _ => ?_
          rw [hIvval v]; ring
        rw [h1]
        congr 1

        have hint : ∀ w ∉ S, cpt K w (centralScalar (𝓞 K) K u) ∈ localIntegralSet K w := by
          intro w hw
          by_cases hw1 : w ∈ S₁
          ·
            have hne : Iv w ≠ 0 := by
              intro h0
              apply hI'0
              rw [hI'S₁, Finset.prod_eq_zero hw1 h0, mul_zero]
            rw [hIvval w] at hne
            simp only [hfv_def, hw, if_false] at hne
            by_contra hn
            rw [cpt_centralScalar] at hn
            rw [Set.indicator_of_notMem hn] at hne
            simp at hne
          · exact (hout w hw1).2.2.2
        rw [hprod _ hint, ← Finset.prod_sdiff hSS₁]
        have h1' : ∏ v ∈ S₁ \ S, fv v (sc (uAt K v u)) = 1 := by
          refine Finset.prod_eq_one fun v hv => ?_
          rw [Finset.mem_sdiff] at hv
          simp only [hfv_def, hv.2, if_false]
          rw [Set.indicator_of_mem]
          rw [← cpt_centralScalar]
          exact hint v hv.2
        rw [h1', one_mul]
        refine Finset.prod_congr rfl fun v hv => ?_
        simp only [hfv_def, hv, if_true, cpt_centralScalar]

      obtain ⟨hfin, heven⟩ := AutomorphicForm.finite_and_even_ncard_places_not_isSigmaConjugate_scalar_of_finrank_eq_two
        K L h2 σ hgen δ₀ hδ₀c
      have hsetF : {v : HeightOneSpectrum (𝓞 K) | ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
          ¬ IsSigmaConjugate K L (v.adicCompletion K) σ
            (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀) (sc z)} =
          ↑(S₁.filter P) := by
        ext v
        rw [Set.mem_setOf_eq, ← hPiff v, Finset.coe_filter, Set.mem_setOf_eq]
        constructor
        · intro hPv
          refine ⟨?_, hPv⟩
          by_contra hv
          exact (hout v hv).1 hPv
        · exact fun h => h.2
      have hsetI : {w : InfinitePlace K | ∀ z : (L ⊗[K] w.Completion)ˣ, ¬ IsSigmaConjugate K L w.Completion σ
          (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] w.Completion) δ₀) (sc z)}.ncard =
          rexp := by
        rw [hrexp_def, ← Nat.card_coe_set_eq]
        congr 2
        ext w
        exact (hQiff w).symm
      rw [hsetF, Set.ncard_coe_finset, hsetI] at heven
      have hsign : (-1 : ℂ) ^ rexp * sgn = 1 := by
        rw [hsgn, ← pow_add, add_comm]
        exact heven.neg_one_pow

      set τaM : Measure (Garch K) := Measure.map ea τc with hτaM_def

      set cτ : ℝ := (r₀ : ℝ) * cK * gA * ∏ v ∈ S₁, (α v : ℝ) with hcτ_def
      have hcτ0 : 0 < cτ := by
        have : 0 < ∏ v ∈ S₁, (α v : ℝ) := Finset.prod_pos fun v _ => by
          have := hα0 v; positivity
        positivity
      have hτprod : ∀ (S' : Finset (HeightOneSpectrum (𝓞 K))), S₁ ⊆ S' →
          ∀ (W : Gad K → ℂ) (Wa : Garch K → ℂ) (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gv K v → ℂ),
          AEStronglyMeasurable Wa τaM →
          (∀ v ∈ S', AEStronglyMeasurable (WS v) (τM v)) →
          (∀ t : Tu u, (∀ v ∉ S', cpt K v (t : Gad K) ∈ localIntegralSet K v) →
              W t = Wa (glArch (𝓞 K) K (t : Gad K)) * ∏ v ∈ S', WS v (cpt K v (t : Gad K))) →
          (∀ t : Tu u, (∃ v ∉ S', cpt K v (t : Gad K) ∉ localIntegralSet K v) → W t = 0) →
            ∫ t, W t ∂τ = cτ * (∫ x, Wa x ∂τaM) * ∏ v ∈ S', ∫ y, WS v y ∂(τM v) := by
        intro S' hS' W Wa WS hWa hWS hfacW hvanW

        have hτν₀ : τ = Measure.map e.symm ν₀ := by
          rw [hν₀_def, Measure.map_map hmes hme]
          have : (e.symm : Gad K → Tu u) ∘ (e : Tu u → Gad K) = id := funext fun s => e.symm_apply_apply s
          rw [this, Measure.map_id]
        have hmee : MeasurableEmbedding (e.symm : Gad K → Tu u) := e.symm.toHomeomorph.measurableEmbedding
        have h1 : ∫ t, W t ∂τ = (r₀ : ℂ) * ∫ g, W (e.symm g) ∂μK := by
          rw [hτν₀, hmee.integral_map, hν₀, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
        have hfa' : AEStronglyMeasurable Wa (archHaarK K) := by
          rw [harchHaar]; exact hWa.smul_measure _
        have hfS' : ∀ v ∈ S', AEStronglyMeasurable (WS v) (localHaar K v) := by
          intro v hv; rw [hHaarα v]; exact (hWS v hv).smul_measure _
        have hfacK : ∀ g : Gad K, (∀ v ∉ S', cpt K v g ∈ localIntegralSet K v) →
            W (e.symm g) = Wa (glArch (𝓞 K) K g) * ∏ v ∈ S', WS v (cpt K v g) := fun g hg => hfacW (e.symm g) hg
        have hvanK : ∀ g : Gad K, (∃ v ∉ S', cpt K v g ∉ localIntegralSet K v) → W (e.symm g) = 0 := fun g hg => hvanW (e.symm g) hg
        have h2 := hG S' (fun g => W (e.symm g)) Wa WS hfa' hfS' hfacK hvanK
        have h3 : ∫ x, Wa x ∂(archHaarK K) = (gA : ℝ) * ∫ x, Wa x ∂τaM := by
          rw [harchHaar, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
        have h4 : ∀ v ∈ S', ∫ y, WS v y ∂(localHaar K v) = (α v : ℝ) * ∫ y, WS v y ∂(τM v) := by
          intro v _
          rw [hHaarα v, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
        have h5 : ∏ v ∈ S', ((α v : ℝ) : ℂ) = ∏ v ∈ S₁, ((α v : ℝ) : ℂ) := by
          rw [← Finset.prod_sdiff hS']
          have : ∏ v ∈ S' \ S₁, ((α v : ℝ) : ℂ) = 1 := Finset.prod_eq_one fun v hv => by
            rw [Finset.mem_sdiff] at hv
            rw [(hout v hv.2).2.1]; simp
          rw [this, one_mul]
        rw [h1, h2, h3, Finset.prod_congr rfl h4, Finset.prod_mul_distrib, h5, hcτ_def]
        push_cast
        ring

      set cτ' : ℝ := cT * ∏ v ∈ S₁, (β v : ℝ) with hcτ'_def
      have hcτ'0 : 0 < cτ' := by
        have : 0 < ∏ v ∈ S₁, (β v : ℝ) := Finset.prod_pos fun v _ => by
          have := hβ0 v; positivity
        positivity
      have hτ'prod : ∀ (S' : Finset (HeightOneSpectrum (𝓞 K))), S₁ ⊆ S' →
          ∀ (W : Gt K L → ℂ) (Wa : Ht K L → ℂ) (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
          AEStronglyMeasurable (fun t : Tda σ δ₀ c => Wa t) τa' →
          (∀ v ∈ S', AEStronglyMeasurable (fun t : Tdv σ δ₀ c v => WS v t) (τM' v)) →
          (∀ t : Td σ δ₀ c, (∀ v ∉ S', tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
              W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S', WS v (tensorPlace K L v (t : Gt K L))) →
          (∀ t : Td σ δ₀ c, (∃ v ∉ S', tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0) →
            ∫ t, W t ∂τ' = cτ' * (∫ t, Wa t ∂τa') * ∏ v ∈ S', ∫ t, WS v t ∂(τM' v) := by
        intro S' hS' W Wa WS hWa hWS hfacW hvanW
        have hWS' : ∀ v ∈ S', AEStronglyMeasurable (fun t : Tdv σ δ₀ c v => WS v t) (τu v) := by
          intro v hv; rw [hτuβ v]; exact (hWS v hv).smul_measure _
        have h2 := hT S' W Wa WS hWa hWS' hfacW hvanW
        have h4 : ∀ v ∈ S', ∫ t, WS v t ∂(τu v) = (β v : ℝ) * ∫ t, WS v t ∂(τM' v) := by
          intro v _
          rw [hτuβ v, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
        have h5 : ∏ v ∈ S', ((β v : ℝ) : ℂ) = ∏ v ∈ S₁, ((β v : ℝ) : ℂ) := by
          rw [← Finset.prod_sdiff hS']
          have : ∏ v ∈ S' \ S₁, ((β v : ℝ) : ℂ) = 1 := Finset.prod_eq_one fun v hv => by
            rw [Finset.mem_sdiff] at hv
            rw [(hout v hv.2).2.2.1]; simp
          rw [this, one_mul]
        rw [h2, Finset.prod_congr rfl h4, Finset.prod_mul_distrib, h5, hcτ'_def]
        push_cast
        ring

      have hgram1' : Measure.map (fun t : Garch K =>
          (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
            (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) τaM =
          Measure.map (fun t : Tua u => ((t : Garch K) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
            (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) τc := by
        have hcont : Continuous (fun t : Garch K => (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
            (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) := by
          have h' : Continuous (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) := by
            have h : Continuous fun a : InfiniteAdeleRing K => a • (1 : L ⊗[K] InfiniteAdeleRing K) := continuous_id.fun_smul continuous_const
            refine h.congr fun a => ?_
            rw [← Algebra.algebraMap_eq_smul_one]; rfl
          exact (continuous_id.matrix_map h').comp Units.continuous_val
        rw [hτaM_def, Measure.map_map hcont.measurable hmea]
        rfl

      have hmass := AutomorphicForm.mul_eq_two_mul_of_forall_isFundamentalDomain_twistedCentralizer_measure_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
        K L h2 σ hgen δ₀ c u hN hns τaM (ea.isHaarMeasure_map τc) τa' hτa'H τM hτMH τM' hτM'H
        ⟨n₁, n₂, e₁, e₂, s, hs0, hstop, hli1, hsp1, hli2, hsp2, hgram1'.trans hgram1, hgram2⟩
        (fun v => hHFin v) S₁ τ hτ cτ hcτ0 hτprod τ' hτ' cτ' hcτ'0 hτ'prod
        ((Module.finrank K L : ℝ≥0∞) * C) C (ENNReal.mul_ne_top (by simp) hCtop) hCtop hD hD'

      have hceq : cτ' = cτ := by
        rw [h2] at hmass
        push_cast at hmass
        have h1 : ENNReal.ofReal cτ' * 2 * C = ENNReal.ofReal cτ * 2 * C := by
          rw [mul_assoc, hmass]; ring
        have h2C : (2 : ℝ≥0∞) * C ≠ 0 := mul_ne_zero two_ne_zero hC0
        have h2Ct : (2 : ℝ≥0∞) * C ≠ ⊤ := ENNReal.mul_ne_top (by simp) hCtop
        rw [mul_assoc, mul_assoc] at h1
        have h3 : ENNReal.ofReal cτ' = ENNReal.ofReal cτ := (ENNReal.mul_left_inj h2C h2Ct).1 h1
        exact (ENNReal.ofReal_eq_ofReal_iff hcτ'0.le hcτ0.le).1 h3

      rw [hI'S₁, hIaval, hprodS₁, hIval, hfu]

      have hkey : (cT : ℂ) * ∏ v ∈ S₁, ((β v : ℝ) : ℂ) = (r₀ : ℂ) * cK * gA * ∏ v ∈ S₁, ((α v : ℝ) : ℂ) := by
        have := congrArg (fun x : ℝ => (x : ℂ)) hceq
        simp only [hcτ_def, hcτ'_def] at this
        push_cast at this
        exact this
      have hκ : κ * ∏ v ∈ S₁, ((β v : ℝ) : ℂ) = ∏ v ∈ S₁, ((α v : ℝ) : ℂ) := by
        rw [hκ_def, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        have hb : ((β v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβ0 v
        push_cast
        field_simp
      have hβprod0 : ∏ v ∈ S₁, ((β v : ℝ) : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => by exact_mod_cast hβ0 v
      have hαprod0 : ∏ v ∈ S₁, ((α v : ℝ) : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => by exact_mod_cast hα0 v
      have hr₀0' : (r₀ : ℂ) ≠ 0 := by exact_mod_cast hr₀0.ne'
      have hcK0 : (cK : ℂ) ≠ 0 := by exact_mod_cast hcK.ne'
      have hcT0 : (cT : ℂ) ≠ 0 := by exact_mod_cast hcT.ne'

      have hκ' : κ = (∏ v ∈ S₁, ((α v : ℝ) : ℂ)) / ∏ v ∈ S₁, ((β v : ℝ) : ℂ) := by
        rw [eq_div_iff hβprod0]; exact hκ
      have hcT' : (cT : ℂ) = (r₀ : ℂ) * cK * gA * (∏ v ∈ S₁, ((α v : ℝ) : ℂ)) / ∏ v ∈ S₁, ((β v : ℝ) : ℂ) := by
        rw [eq_div_iff hβprod0]; exact hkey
      have hsgnκ : (-1 : ℂ) ^ rexp * sgn * κ * ((cK : ℂ) * cL * gA) = cL * cT * (((r₀⁻¹ : ℝ≥0) : ℝ) : ℂ) := by
        rw [hsign, one_mul, hκ', hcT']
        push_cast
        field_simp
      set FF : ℂ := ff (glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) with hFF
      set FA : ℂ := fa (sc (uArch K u)) with hFA
      calc (cK : ℂ) * ((cL : ℂ) * ((cT⁻¹ : ℝ) : ℂ) * ((-1 : ℂ) ^ rexp * (FA * (gA : ℂ))) * (sgn * κ * FF))
          = ((-1 : ℂ) ^ rexp * sgn * κ * ((cK : ℂ) * cL * gA)) * ((cT⁻¹ : ℝ) : ℂ) * (FA * FF) := by ring
        _ = (cL * cT * (((r₀⁻¹ : ℝ≥0) : ℝ) : ℂ)) * ((cT⁻¹ : ℝ) : ℂ) * (FA * FF) := by rw [hsgnκ]
        _ = cL * (FA * FF * (((r₀⁻¹ : ℝ≥0) : ℝ) : ℂ)) := by
              push_cast
              field_simp

end Main

end AutomorphicForm.CentralQuaternion
p2m_reactivate "P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm.CentralQuaternion"
p2m_reactivate "P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm.CentralQuaternion"

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open AutomorphicForm.CentralQuaternion in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (μK : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hμK : μK.IsHaarMeasure)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μL)
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
          ∫ g, f g ∂μK = cK * (∫ x, fa x ∂(AutomorphicForm.archHaarK K)) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
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
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ w : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = v → Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (hArch : AutomorphicForm.AreMatchingArch K L σ φa fa)
    (hLoc : ∀ v ∈ S, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (fS v))
    (hunit : ∀ v ∉ S, AutomorphicForm.AreMatchingLocal K L v σ
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (τ : Measure (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : τ.IsHaarMeasure) (hτ' : τ'.IsHaarMeasure)
    (C : ENNReal) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
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
          C * ENNReal.ofReal (Real.log (b / a)))
    (hD : ∀ D : Set (Subgroup.centralizer
        ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
      IsFundamentalDomain
        (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
          (Subgroup.centralizer
            ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op D τ →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
          (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
          (Module.finrank K L : ENNReal) * C * ENNReal.ofReal (Real.log (b / a)))
    (I I' : ℂ)
    (hI' : AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μL
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ'
      (φ ∘ Matrix.GeneralLinearGroup.map (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) I')
    (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μK (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I) :
    (cK : ℂ) * I' = cL * I := by
  haveI := hμK
  haveI : μL.IsHaarMeasure := hμL
  haveI : τ.IsHaarMeasure := hτ
  haveI : τ'.IsHaarMeasure := hτ'
  exact main h2 σ hσ μK μL cK cL hcK hcL hG hG' S φ f φa φf φS fa ff fS hφ hf hArch hLoc hunit δ₀ c u hN hns τ τ'
    C hC0 hCtop hD' hD I I' hI' hI

end S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two (solution)
