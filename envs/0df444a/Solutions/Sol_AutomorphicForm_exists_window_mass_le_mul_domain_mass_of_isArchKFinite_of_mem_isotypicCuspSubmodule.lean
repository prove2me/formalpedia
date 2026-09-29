-- Prove2me | solution 1 for AutomorphicForm.exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9f7207c0-a7e6-5e2a-b840-f33e2e023105

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_AutomorphicForm_exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike"
p2m_attr_erase "instance" "SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply"
p2m_attr_erase "simp" "IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.iotaZsqrtdNegTwo_apply"
set_option autoImplicit false
open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel

section SlabInvariance

open Set NumberField.AdelicLevel NumberField.AdelicHaar NumberField.TateGlobal

variable {F : Type} [Field F] [NumberField F]

private theorem countable_of_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

private theorem countable_globalPoints_range : Countable (globalPoints (𝓞 F) F).range := by
  haveI : Countable F := countable_of_numberField
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (GL (Fin 2) F) := Units.val_injective.countable
  exact (Set.countable_range (globalPoints (𝓞 F) F)).to_subtype

private theorem measurableConstSMul_globalPoints_range :
    MeasurableConstSMul (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  refine ⟨fun γ => ?_⟩
  simpa only [Subgroup.smul_def, smul_eq_mul] using
    (show Continuous fun x : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * x from
      continuous_const.mul continuous_id).measurable

private theorem preimage_globalPoints_mul_slab (γ : (globalPoints (𝓞 F) F).range) (a b : ℝ) :
    (fun x : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * x) ⁻¹'
        {g | ideleNorm F (GeneralLinearGroup.det g) ∈ Icc a b}
      = {g | ideleNorm F (GeneralLinearGroup.det g) ∈ Icc a b} := by
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, ← hγ₀, map_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

private theorem smulInvariantMeasure_restrict_slab (a b : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (GeneralLinearGroup.det g) ∈ Icc a b}) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  simp only [Subgroup.smul_def, smul_eq_mul]
  have hm : Measurable fun x : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * x :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.restrict_apply (hs.preimage hm), Measure.restrict_apply hs,
    ← preimage_globalPoints_mul_slab γ a b, ← Set.preimage_inter, measure_preimage_mul,
    preimage_globalPoints_mul_slab γ a b]

private theorem setLIntegral_image_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulRightInvariant] (F : G → ℝ≥0∞) {S : Set G} (hS : MeasurableSet S) (x : G) :
    ∫⁻ y in (· * x) '' S, F y ∂μ = ∫⁻ y in S, F (y * x) ∂μ := by
  have hpre : MeasurableSet ((· * x⁻¹) ⁻¹' S) := hS.preimage (measurable_mul_const x⁻¹)
  rw [Set.image_mul_right, ← lintegral_indicator hpre, ← lintegral_indicator hS,
    ← lintegral_mul_right_eq_self (((· * x⁻¹) ⁻¹' S).indicator F) x]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · have hy' : y * x ∈ (· * x⁻¹) ⁻¹' S := by simpa [Set.mem_preimage] using hy
    simp [Set.indicator, hy, hy']
  · have hy' : y * x ∉ (· * x⁻¹) ⁻¹' S := by simpa [Set.mem_preimage] using hy
    simp [Set.indicator, hy, hy']

private theorem setLIntegral_image_mul_centralScalar {χ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F ⊤ χ φ) {W : Set (AdelicGL2 (𝓞 F) F)}
    (hW : MeasurableSet W) (z : (AdeleRing (𝓞 F) F)ˣ) :
    ∫⁻ y in (· * centralScalar (𝓞 F) F z) '' W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ((‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞)) ^ 2 *
          ∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isMulRightInvariant_adelicGLHaar F
  rw [setLIntegral_image_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) _ hW, ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun hW fun y _ => ?_
  rw [mul_centralScalar_comm, hφ.central_transform ⟨z, Subgroup.mem_top z⟩ y, nnnorm_mul, ENNReal.coe_mul, mul_pow]

end SlabInvariance

section DeterminantNormBand

open Set NumberField.AdelicLevel NumberField.AdelicVolume NumberField.TateGlobal

variable {K : Type} [Field K] [NumberField K]

private theorem ideleNorm_det_eq_prod_archDetNorm_pow (X : AdelicGL2 (𝓞 K) K)
    (hX : glFin (𝓞 K) K X ∈ finiteIntegralGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det X)
      = ∏ w : InfinitePlace K, archDetNorm w X ^ w.mult := by
  exact NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K X hX

private theorem exists_bounds_ideleNorm_det (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ x ∈ T, ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Icc a b := by
  classical
  set N : Finset ℝ :=
    insert (1 : ℝ) (T.image fun x : AdelicGL2 (𝓞 K) K => ideleNorm K (Matrix.GeneralLinearGroup.det x))
  have hNne : N.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hpos : ∀ r ∈ N, 0 < r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact one_pos
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hr
      exact ideleNorm_pos _
  refine ⟨N.min' hNne, N.max' hNne, hpos _ (N.min'_mem hNne), N.min'_le_max' hNne,
    fun x hx => ?_⟩
  have hmem : ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ N :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)
  exact ⟨N.min'_le _ hmem, N.le_max' _ hmem⟩

private theorem prod_pow_mult_pos {d : ℝ} (hd : 0 < d) : 0 < ∏ w : InfinitePlace K, d ^ w.mult :=
  Finset.prod_pos fun _ _ => pow_pos hd _

private theorem ideleNorm_det_mem_of_mem_centreCutSiegelSetAmple {c u d₁ d₂ κ : ℝ} (hd₁ : 0 < d₁)
    {h : AdelicGL2 (𝓞 K) K} (hh : h ∈ centreCutSiegelSetAmple K c u d₁ d₂ κ) :
    ideleNorm K (Matrix.GeneralLinearGroup.det h) ∈
      Icc (∏ w : InfinitePlace K, d₁ ^ w.mult) (∏ w : InfinitePlace K, d₂ ^ w.mult) := by
  have hint : glFin (𝓞 K) K h ∈ finiteIntegralGL2 (𝓞 K) K := (mem_centreCutSiegelSet_iff.mp hh.1).1
  have hwindow : ∀ v : InfinitePlace K, archDetNorm v h ∈ Icc d₁ d₂ := hh.1.2.2.2
  rw [ideleNorm_det_eq_prod_archDetNorm_pow h hint]
  constructor
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg hd₁.le _)
      (fun w _ => pow_le_pow_left₀ hd₁.le (hwindow w).1 _)
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w h).le _)
      (fun w _ => pow_le_pow_left₀ (archDetNorm_pos w h).le (hwindow w).2 _)

end DeterminantNormBand

section Transport

open Set NumberField.AdelicLevel NumberField.AdelicHaar NumberField.TateGlobal
open scoped Pointwise

variable {K : Type} [Field K] [NumberField K]

private theorem setLIntegral_biUnion_le_sum {G ι : Type} [MeasurableSpace G] (μ : Measure G) (f : G → ℝ≥0∞)
    (V : ι → Set G) (I : Finset ι) : ∫⁻ y in ⋃ i ∈ I, V i, f y ∂μ ≤ ∑ i ∈ I, ∫⁻ y in V i, f y ∂μ := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (by gcongr)

private theorem exists_nat_forall_mem_Icc_exists_lt_mem_Icc_mul_pow {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (b : ℝ) :
    ∃ n : ℕ, ∀ v ∈ Icc a b, ∃ i < n, v ∈ Icc (a * r ^ i) (a * r ^ (i + 1)) := by
  have key : ∀ m : ℕ, ∀ v : ℝ, a ≤ v → v ≤ a * r ^ m → ∃ i < m + 1, v ∈ Icc (a * r ^ i) (a * r ^ (i + 1)) := by
    intro m
    induction m with
    | zero =>
      intro v hav hva
      refine ⟨0, Nat.zero_lt_one, ?_, ?_⟩
      · simpa using hav
      · rw [pow_zero, mul_one] at hva
        rw [zero_add, pow_one]
        exact hva.trans (le_mul_of_one_le_right ha.le hr.le)
    | succ m ih =>
      intro v hav hvm
      by_cases hv : v ≤ a * r ^ m
      · obtain ⟨i, hi, hmem⟩ := ih v hav hv
        exact ⟨i, hi.trans (Nat.lt_succ_self _), hmem⟩
      · exact ⟨m, by omega, (not_le.1 hv).le, hvm⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b / a) hr
  refine ⟨n + 1, fun v hv => ?_⟩
  have hb : b < r ^ n * a := (div_lt_iff₀ ha).1 hn
  exact key n v hv.1 (by nlinarith [hv.2, hb])

private theorem exists_pos_forall_mem_translates_ideleNorm_det_mem_Icc (c u d₁ d₂ κ : ℝ) (hd₁ : 0 < d₁)
    (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ a b : ℝ, 0 < a ∧ ∀ g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ,
      ideleNorm K (GeneralLinearGroup.det g) ∈ Icc a b := by
  obtain ⟨a, b, ha, -, hT⟩ := exists_bounds_ideleNorm_det (K := K) T
  have hP₁ : 0 < ∏ w : InfinitePlace K, d₁ ^ w.mult := prod_pow_mult_pos hd₁
  refine ⟨(∏ w : InfinitePlace K, d₁ ^ w.mult) * a, (∏ w : InfinitePlace K, d₂ ^ w.mult) * b, mul_pos hP₁ ha,
    fun g hg => ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image] at hg
  obtain ⟨x, hx, h, hh, rfl⟩ := hg
  have hh' := ideleNorm_det_mem_of_mem_centreCutSiegelSetAmple hd₁ hh
  have hx' := hT x hx
  rw [map_mul, ideleNorm_mul]
  exact ⟨mul_le_mul hh'.1 hx'.1 ha.le (hP₁.le.trans hh'.1),
    mul_le_mul hh'.2 hx'.2 (ideleNorm_pos _).le ((hP₁.le.trans hh'.1).trans hh'.2)⟩

private theorem exists_forall_ideleNorm_det_mul_centralScalar_eq {s : ℝ} (hs : 0 < s) :
    ∃ z : (AdeleRing (𝓞 K) K)ˣ, ∀ y : AdelicGL2 (𝓞 K) K,
      ideleNorm K (GeneralLinearGroup.det (y * centralScalar (𝓞 K) K z))
        = ideleNorm K (GeneralLinearGroup.det y) * s := by
  obtain ⟨z, -, hz⟩ := exists_ideleNorm_eq_and_snd_eq_one K (Real.sqrt s) (Real.sqrt_pos.2 hs)
  refine ⟨z, fun y => ?_⟩
  rw [map_mul, det_centralScalar K z, ideleNorm_mul, pow_two, ideleNorm_mul, hz, Real.mul_self_sqrt hs.le]

private theorem finite_and_ncard_image_mul_right_le {W V : Set (AdelicGL2 (𝓞 K) K)} (hVW : V ⊆ W) {M : ℕ}
    (hM : ∀ y : AdelicGL2 (𝓞 K) K, {γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ W}.Finite ∧
      {γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ W}.ncard ≤ M)
    (ζ : AdelicGL2 (𝓞 K) K) (y : AdelicGL2 (𝓞 K) K) :
    {γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ (· * ζ) '' V}.Finite ∧
      {γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ (· * ζ) '' V}.ncard ≤ M := by
  obtain ⟨hfin, hcard⟩ := hM (y * ζ⁻¹)
  have hsub : {γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ (· * ζ) '' V} ⊆
      {γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * (y * ζ⁻¹) ∈ W} := by
    intro γ hγ
    rw [Set.mem_setOf_eq, Set.image_mul_right, Set.mem_preimage] at hγ
    rw [Set.mem_setOf_eq, ← mul_assoc]
    exact hVW hγ
  exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans hcard⟩

private theorem setLIntegral_le_mul_setLIntegral_of_forall_ncard_le (α β : ℝ) {X S : Set (AdelicGL2 (𝓞 K) K)}
    (hXm : MeasurableSet X) (hXs : X ⊆ {g | ideleNorm K (GeneralLinearGroup.det g) ∈ Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 K) K).range S
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict {g | ideleNorm K (GeneralLinearGroup.det g) ∈ Icc α β}))
    (M : ℕ)
    (hM : ∀ y : AdelicGL2 (𝓞 K) K, {γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ X}.Finite ∧
      {γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ X}.ncard ≤ M)
    (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * g) = f g) :
    ∫⁻ y in X, f y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤ M * ∫⁻ y in S, f y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  set slab : Set (AdelicGL2 (𝓞 K) K) :=
    {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hslabdef
  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμdef
  have hslab : MeasurableSet slab := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β
  haveI : Countable (globalPoints (𝓞 K) K).range := countable_globalPoints_range
  haveI : MeasurableConstSMul (globalPoints (𝓞 K) K).range (AdelicGL2 (𝓞 K) K) :=
    measurableConstSMul_globalPoints_range
  haveI : SMulInvariantMeasure ↥(globalPoints (𝓞 K) K).range (AdelicGL2 (𝓞 K) K) (μ.restrict slab) :=
    smulInvariantMeasure_restrict_slab α β
  have hνW : (μ.restrict slab).restrict X = μ.restrict X := by
    rw [Measure.restrict_restrict' hslab, Set.inter_eq_left.mpr hXs]
  have hfg : ∀ (g : ↥(globalPoints (𝓞 K) K).range) (y : AdelicGL2 (𝓞 K) K), f (g⁻¹ • y) = f y := fun g y => by
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp (g⁻¹).2
    rw [Subgroup.smul_def, smul_eq_mul, ← hγ]
    exact hinv γ y
  have hcount : ∀ y : AdelicGL2 (𝓞 K) K, ({g : ↥(globalPoints (𝓞 K) K).range | y ∈ g • X}).encard ≤ (M : ℕ∞) := by
    intro y
    obtain ⟨hfin, hcard⟩ := hM y
    calc ({g : ↥(globalPoints (𝓞 K) K).range | y ∈ g • X}).encard
        ≤ ((fun γ : GL (Fin 2) K =>
              (⟨globalPoints (𝓞 K) K γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩⟩ : ↥(globalPoints (𝓞 K) K).range)⁻¹) ''
            {γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ X}).encard := by
          refine Set.encard_le_encard fun g hg => ?_
          obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp (g⁻¹).2
          refine ⟨γ, ?_, ?_⟩
          · have hg' := Set.mem_smul_set_iff_inv_smul_mem.mp hg
            rw [Subgroup.smul_def, smul_eq_mul, ← hγ] at hg'
            exact hg'
          · have hg'' : (⟨globalPoints (𝓞 K) K γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩⟩ :
                ↥(globalPoints (𝓞 K) K).range) = g⁻¹ := Subtype.ext hγ
            show (⟨globalPoints (𝓞 K) K γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩⟩ :
                ↥(globalPoints (𝓞 K) K).range)⁻¹ = g
            rw [hg'', inv_inv]
      _ ≤ ({γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ X}).encard := Set.encard_image_le _ _
      _ = (({γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ X}).ncard : ℕ∞) := hfin.cast_ncard_eq.symm
      _ ≤ (M : ℕ∞) := by exact_mod_cast hcard
  calc ∫⁻ y in X, f y ∂μ = ∫⁻ y in X, f y ∂(μ.restrict slab) := by rw [hνW]
    _ = ∑' g : ↥(globalPoints (𝓞 K) K).range, ∫⁻ y in g • X ∩ S, f (g⁻¹ • y) ∂(μ.restrict slab) :=
        hS.setLIntegral_eq_tsum' f X
    _ = ∑' g : ↥(globalPoints (𝓞 K) K).range, ∫⁻ y in S, (g • X).indicator f y ∂(μ.restrict slab) := by
        refine tsum_congr fun g => ?_
        simp_rw [hfg g]
        rw [lintegral_indicator (hXm.const_smul g), Measure.restrict_restrict (hXm.const_smul g)]
    _ = ∫⁻ y in S, ∑' g : ↥(globalPoints (𝓞 K) K).range, (g • X).indicator f y ∂(μ.restrict slab) :=
        (lintegral_tsum fun g => (hf.indicator (hXm.const_smul g)).aemeasurable).symm
    _ ≤ ∫⁻ y in S, (M : ℝ≥0∞) * f y ∂(μ.restrict slab) := by
        refine lintegral_mono fun y => ?_
        have h1 : ∀ g : ↥(globalPoints (𝓞 K) K).range,
            (g • X).indicator f y = ({g : ↥(globalPoints (𝓞 K) K).range | y ∈ g • X}).indicator (fun _ => f y) g := by
          intro g
          by_cases hg : y ∈ g • X <;> simp [Set.indicator, hg]
        simp_rw [h1]
        rw [← tsum_subtype, ENNReal.tsum_set_const]
        refine mul_le_mul_left ?_ _
        have h2 := ENat.toENNReal_le.mpr (hcount y)
        simpa using h2
    _ = M * ∫⁻ y in S, f y ∂(μ.restrict slab) := lintegral_const_mul _ hf
    _ ≤ M * ∫⁻ y in S, f y ∂μ :=
        mul_le_mul' le_rfl (lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl)

private theorem setLIntegral_nnnorm_sq_le_inv_mul_mul_of_image_mul_centralScalar_subset (α β : ℝ)
    {S : Set (AdelicGL2 (𝓞 K) K)}
    (hS : IsFundamentalDomain (globalPoints (𝓞 K) K).range S
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict {g | ideleNorm K (GeneralLinearGroup.det g) ∈ Icc α β}))
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (hφc : Continuous φ) {W V : Set (AdelicGL2 (𝓞 K) K)}
    (hVm : MeasurableSet V) (hVW : V ⊆ W) {M : ℕ}
    (hM : ∀ y : AdelicGL2 (𝓞 K) K, {γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ W}.Finite ∧
      {γ : GL (Fin 2) K | globalPoints (𝓞 K) K γ * y ∈ W}.ncard ≤ M)
    (z : (AdeleRing (𝓞 K) K)ˣ)
    (hVz : (· * centralScalar (𝓞 K) K z) '' V ⊆ {g | ideleNorm K (GeneralLinearGroup.det g) ∈ Icc α β}) :
    ∫⁻ y in V, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ((‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2)⁻¹ * M
          * ∫⁻ y in S, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  set k : ℝ≥0∞ := (‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2
  have hk0 : k ≠ 0 := pow_ne_zero 2 (ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 (Units.ne_zero _)))
  have hktop : k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hVzm : MeasurableSet ((· * centralScalar (𝓞 K) K z) '' V) := by
    rw [Set.image_mul_right]
    exact hVm.preimage (measurable_mul_const _)
  have hf : Measurable fun y : AdelicGL2 (𝓞 K) K => (‖φ y‖₊ : ℝ≥0∞) ^ 2 :=
    (hφc.measurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      (‖φ (globalPoints (𝓞 K) K γ * g)‖₊ : ℝ≥0∞) ^ 2 = (‖φ g‖₊ : ℝ≥0∞) ^ 2 := by
    intro γ g
    rw [hφ.left_invariant γ g]
  have hdom : ∫⁻ y in (· * centralScalar (𝓞 K) K z) '' V, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ M * ∫⁻ y in S, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
    setLIntegral_le_mul_setLIntegral_of_forall_ncard_le α β hVzm hVz hS M
      (finite_and_ncard_image_mul_right_le hVW hM (centralScalar (𝓞 K) K z)) _ hf hinv
  rw [setLIntegral_image_mul_centralScalar hφ hVm z] at hdom
  calc ∫⁻ y in V, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = k⁻¹ * (k * ∫⁻ y in V, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) :=
        (ENNReal.inv_mul_cancel_left hk0 hktop).symm
    _ ≤ k⁻¹ * (M * ∫⁻ y in S, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := mul_le_mul' le_rfl hdom
    _ = k⁻¹ * M * ∫⁻ y in S, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := (mul_assoc _ _ _).symm

private theorem exists_forall_setLIntegral_translates_ample_le_mul_setLIntegral_of_mem_isotypicCuspSubmodule
    (c u d₁ d₂ κ : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c) (hd₁ : 0 < d₁) (T : Finset (AdelicGL2 (𝓞 K) K)) (α β : ℝ)
    (hβ : 0 < β) (hαβ : α < β) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict {g | ideleNorm K (GeneralLinearGroup.det g) ∈ Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ g ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ,
        ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ, (‖g x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ C * ∫⁻ x in Φ₀, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμdef
  set W : Set (AdelicGL2 (𝓞 K) K) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ with hWdef
  have hWm : MeasurableSet W := by
    refine MeasurableSet.biUnion T.countable_toSet fun x _ => ?_
    rw [Set.image_mul_right]
    exact (measurableSet_centreCutSiegelSetAmple c u d₁ d₂ κ).preimage (measurable_mul_const _)
  obtain ⟨M, hM⟩ :=
    AutomorphicForm.exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le K c u d₁ d₂ κ
      hκ hc hd₁ T
  obtain ⟨a, b, ha, hab⟩ := exists_pos_forall_mem_translates_ideleNorm_det_mem_Icc c u d₁ d₂ κ hd₁ T
  set α' : ℝ := max α (β / 2) with hα'def
  have hα'pos : 0 < α' := lt_max_of_lt_right (half_pos hβ)
  have hα'lt : α' < β := max_lt hαβ (half_lt_self hβ)
  have hαα' : α ≤ α' := le_max_left _ _
  set r : ℝ := β / α' with hrdef
  have hr : 1 < r := (one_lt_div hα'pos).2 hα'lt
  have hrα' : r * α' = β := div_mul_cancel₀ β hα'pos.ne'
  have hr0 : 0 < r := zero_lt_one.trans hr
  obtain ⟨n, hn⟩ := exists_nat_forall_mem_Icc_exists_lt_mem_Icc_mul_pow ha hr b
  have hs : ∀ i : ℕ, 0 < α' / (a * r ^ i) := fun i => div_pos hα'pos (mul_pos ha (pow_pos hr0 i))
  choose z hz using fun i : ℕ => exists_forall_ideleNorm_det_mul_centralScalar_eq (K := K) (hs i)
  set P : ℕ → Set (AdelicGL2 (𝓞 K) K) :=
    fun i => {y | ideleNorm K (GeneralLinearGroup.det y) ∈ Icc (a * r ^ i) (a * r ^ (i + 1))} with hPdef
  have hPm : ∀ i, MeasurableSet (W ∩ P i) := fun i => hWm.inter (measurableSet_setOf_ideleNorm_det_mem_Icc K _ _)
  have hcover : W ⊆ ⋃ i ∈ Finset.range n, W ∩ P i := by
    intro y hy
    obtain ⟨i, hi, hmem⟩ := hn _ (hab y hy)
    exact Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, hy, hmem⟩
  have hPz : ∀ i, (· * centralScalar (𝓞 K) K (z i)) '' (W ∩ P i) ⊆
      {g | ideleNorm K (GeneralLinearGroup.det g) ∈ Icc α β} := by
    rintro i _ ⟨y, ⟨-, hyP⟩, rfl⟩
    have hy : ideleNorm K (GeneralLinearGroup.det y) ∈ Icc (a * r ^ i) (a * r ^ (i + 1)) := hyP
    have hpos : 0 < a * r ^ i := mul_pos ha (pow_pos hr0 i)
    have hcancel : a * r ^ i * (α' / (a * r ^ i)) = α' := mul_div_cancel₀ α' hpos.ne'
    show ideleNorm K (GeneralLinearGroup.det (y * centralScalar (𝓞 K) K (z i))) ∈ Icc α β
    rw [hz i y]
    refine ⟨hαα'.trans ?_, ?_⟩
    · calc α' = a * r ^ i * (α' / (a * r ^ i)) := hcancel.symm
        _ ≤ ideleNorm K (GeneralLinearGroup.det y) * (α' / (a * r ^ i)) :=
            mul_le_mul_of_nonneg_right hy.1 (hs i).le
    · calc ideleNorm K (GeneralLinearGroup.det y) * (α' / (a * r ^ i))
          ≤ a * r ^ (i + 1) * (α' / (a * r ^ i)) := mul_le_mul_of_nonneg_right hy.2 (hs i).le
        _ = r * (a * r ^ i * (α' / (a * r ^ i))) := by ring
        _ = β := by rw [hcancel, hrα']
  refine ⟨∑ i ∈ Finset.range n, ((‖((ξ ⟨z i, Subgroup.mem_top (z i)⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2)⁻¹ * M, ?_,
    fun g hg => ?_⟩
  · refine ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top ?_ (ENNReal.natCast_ne_top M)
    exact ENNReal.inv_ne_top.2 (pow_ne_zero 2 (ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 (Units.ne_zero _))))
  · by_cases hg0 : g = 0
    · subst hg0
      simp
    have hP := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule K Φ₀
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) ξ N S Ψ g hg hg0
    have hlsxi : IsLsXiFunction (𝓞 K) K ⊤ ξ g := ((lsXiMemberAt_iff _ _ _ _ _ _ _).mp hP.smoothCusp.1.1).1
    calc ∫⁻ x in W, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ
        ≤ ∫⁻ x in ⋃ i ∈ Finset.range n, W ∩ P i, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ := lintegral_mono_set hcover
      _ ≤ ∑ i ∈ Finset.range n, ∫⁻ x in W ∩ P i, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ := setLIntegral_biUnion_le_sum μ _ _ _
      _ ≤ ∑ i ∈ Finset.range n, ((‖((ξ ⟨z i, Subgroup.mem_top (z i)⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2)⁻¹ * M
            * ∫⁻ x in Φ₀, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ :=
          Finset.sum_le_sum fun i _ =>
            setLIntegral_nnnorm_sq_le_inv_mul_mul_of_image_mul_centralScalar_subset α β hΦ₀ hlsxi hP.continuous
              (hPm i) Set.inter_subset_left hM (z i) (hPz i)
      _ = (∑ i ∈ Finset.range n, ((‖((ξ ⟨z i, Subgroup.mem_top (z i)⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2)⁻¹ * M)
            * ∫⁻ x in Φ₀, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
          rw [Finset.sum_mul]

end Transport

theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ g ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ,
        IsArchKFinite K g →
          ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖g x‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
            ≤ C * ∫⁻ x in Φ₀, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨κ, hκ, u', C₁, hC₁, hB⟩ :=
    AutomorphicForm.exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule K c u d₁ d₂ T hc hd₁ α β
      hβ hαβ Φ₀ hΦ₀ ξ N hN S Ψ
  obtain ⟨C₂, hC₂, hA⟩ :=
    exists_forall_setLIntegral_translates_ample_le_mul_setLIntegral_of_mem_isotypicCuspSubmodule c u' d₁ d₂ κ hκ hc
      hd₁ T α β hβ hαβ Φ₀ hΦ₀ ξ N S Ψ
  refine ⟨C₁ * C₂, ENNReal.mul_ne_top hC₁ hC₂, fun g hg _ => ?_⟩
  calc _ ≤ C₁ * ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁ d₂ κ, (‖g x‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := hB g hg
    _ ≤ C₁ * (C₂ * ∫⁻ x in Φ₀, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := mul_le_mul' le_rfl (hA g hg)
    _ = C₁ * C₂ * ∫⁻ x in Φ₀, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := (mul_assoc _ _ _).symm

end S_AutomorphicForm_exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule (solution)
