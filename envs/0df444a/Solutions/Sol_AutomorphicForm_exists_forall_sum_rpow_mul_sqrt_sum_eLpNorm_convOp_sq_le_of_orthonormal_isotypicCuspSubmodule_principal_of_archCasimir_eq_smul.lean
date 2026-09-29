-- Prove2me | solution 1 for AutomorphicForm.exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/422efdc8-d18b-5354-8dae-277078f9f972

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_forall_sum_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAt_convOp_eq_convOp_of_isReal
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex
import Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightConv_eq_smul_of_archCasimirAtComplex_eq_smul_of_isArchSmoothAtComplex_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_archCasimirAt_rightConv_eq_smul_of_archCasimirAt_eq_smul_of_isArchSmoothAt_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val HeckePair.IsGelfandInvolution.reindex_mk"
p2m_attr_erase "simp" "HeckePair.IsGelfandInvolution.reindexInv_mk SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff"
p2m_attr_erase "simp" "M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.TateLocal.conductorExponentAt_one"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace DecayHSAssembly

variable {K : Type} [Field K] [NumberField K]

theorem exists_iterate_shift_real (w : InfinitePlace K) (hw : w.IsReal)
    (U : Subgroup (AdelicGL2 (𝓞 K) K)) (hU : U ≤ finiteAdelicGL2Subgroup K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) (hfU : IsBiInvariantUnder K U f) (k : ℕ) :
    ∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsBiInvariantUnder K U β ∧
      ∀ x : AdelicGL2 (𝓞 K) K → ℂ, Continuous x → IsArchSmoothAt hw x → ∀ lam : ℂ,
        archCasimirAt hw x = lam • x → convOp K β x = lam ^ k • convOp K f x := by
  induction k with
  | zero => exact ⟨f, hff, hfU, fun x _ _ lam _ => by rw [pow_zero, one_smul]⟩
  | succ k ih =>
    obtain ⟨β, hβ, hβU, hβk⟩ := ih
    obtain ⟨β', hβ', hβ'U, hshift⟩ :=
      AutomorphicForm.exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAt_convOp_eq_convOp_of_isReal
        K w hw U hU β hβ hβU
    refine ⟨β', hβ', hβ'U, fun x hx hxs lam hxl => ?_⟩
    have h1 := (hshift x hx).2
    have h2 := (AutomorphicForm.archCasimirAt_rightConv_eq_smul_of_archCasimirAt_eq_smul_of_isArchSmoothAt_of_isFactorizableTestFn
      K w hw x hx hxs lam hxl β hβ).2

    rw [← h1, convOp_apply, h2, ← convOp_apply, hβk x hx hxs lam hxl, smul_smul, pow_succ, mul_comm]

theorem exists_iterate_shift_complex (w : InfinitePlace K) (hw : w.IsComplex)
    (U : Subgroup (AdelicGL2 (𝓞 K) K)) (hU : U ≤ finiteAdelicGL2Subgroup K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) (hfU : IsBiInvariantUnder K U f) (k : ℕ) :
    ∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsBiInvariantUnder K U β ∧
      ∀ x : AdelicGL2 (𝓞 K) K → ℂ, Continuous x → IsArchSmoothAtComplex hw x →
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) →
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) →
        ∀ lam lam' : ℂ, archCasimirAtComplex hw x = lam • x → archCasimirBarAtComplex hw x = lam' • x →
          convOp K β x = lam ^ k • convOp K f x := by
  induction k with
  | zero => exact ⟨f, hff, hfU, fun x _ _ _ _ lam lam' _ _ => by rw [pow_zero, one_smul]⟩
  | succ k ih =>
    obtain ⟨β, hβ, hβU, hβk⟩ := ih
    obtain ⟨β', βb', hβ', hβ'U, -, -, hshift⟩ :=
      AutomorphicForm.exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex
        K w hw U hU β hβ hβU
    refine ⟨β', hβ', hβ'U, fun x hx hxs hD1 hD2 lam lam' hxl hxl' => ?_⟩
    have h1 := (hshift x hx).2.1
    have h2 := (AutomorphicForm.archCasimirAtComplex_rightConv_eq_smul_of_archCasimirAtComplex_eq_smul_of_isArchSmoothAtComplex_of_isFactorizableTestFn
      K w hw x hx hxs hD1 hD2 lam lam' hxl hxl' β hβ).2.1
    rw [← h1, convOp_apply, h2, ← convOp_apply, hβk x hx hxs hD1 hD2 lam lam' hxl hxl', smul_smul, pow_succ, mul_comm]

theorem exists_iterate_shift_complex_bar (w : InfinitePlace K) (hw : w.IsComplex)
    (U : Subgroup (AdelicGL2 (𝓞 K) K)) (hU : U ≤ finiteAdelicGL2Subgroup K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) (hfU : IsBiInvariantUnder K U f) (k : ℕ) :
    ∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsBiInvariantUnder K U β ∧
      ∀ x : AdelicGL2 (𝓞 K) K → ℂ, Continuous x → IsArchSmoothAtComplex hw x →
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) →
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) →
        ∀ lam lam' : ℂ, archCasimirAtComplex hw x = lam • x → archCasimirBarAtComplex hw x = lam' • x →
          convOp K β x = lam' ^ k • convOp K f x := by
  induction k with
  | zero => exact ⟨f, hff, hfU, fun x _ _ _ _ lam lam' _ _ => by rw [pow_zero, one_smul]⟩
  | succ k ih =>
    obtain ⟨β, hβ, hβU, hβk⟩ := ih
    obtain ⟨β', βb', -, -, hβb', hβb'U, hshift⟩ :=
      AutomorphicForm.exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex
        K w hw U hU β hβ hβU
    refine ⟨βb', hβb', hβb'U, fun x hx hxs hD1 hD2 lam lam' hxl hxl' => ?_⟩
    have h1 := (hshift x hx).2.2
    have h2 := (AutomorphicForm.archCasimirAtComplex_rightConv_eq_smul_of_archCasimirAtComplex_eq_smul_of_isArchSmoothAtComplex_of_isFactorizableTestFn
      K w hw x hx hxs hD1 hD2 lam lam' hxl hxl' β hβ).2.2
    rw [← h1, convOp_apply, h2, ← convOp_apply, hβk x hx hxs hD1 hD2 lam lam' hxl hxl', smul_smul, pow_succ, mul_comm]

theorem one_add_sum_rpow_le {σ : Type} [Fintype σ] (v : σ → ℝ) (hv : ∀ j, 0 ≤ v j) (s : ℝ) (hs : 0 ≤ s) :
    (1 + ∑ j, v j) ^ s ≤ ((Fintype.card σ : ℝ) + 1) ^ s * (1 + ∑ j, v j ^ s) := by
  classical
  set u : Option σ → ℝ := fun o => o.elim 1 v with hu
  have hu0 : ∀ o, 0 ≤ u o := fun o => by cases o <;> simp [hu, hv]
  have hne : (Finset.univ : Finset (Option σ)).Nonempty := Finset.univ_nonempty
  set T : ℝ := Finset.univ.sup' hne u with hT
  have hle : ∀ o, u o ≤ T := fun o => Finset.le_sup' u (Finset.mem_univ o)
  obtain ⟨o₀, -, ho₀⟩ := Finset.exists_mem_eq_sup' hne u
  have hT0 : 0 ≤ T := (hu0 none).trans (hle none)
  have hsumu : ∑ o, u o = 1 + ∑ j, v j := by
    rw [Fintype.sum_option]; rfl
  have hsumus : ∑ o, u o ^ s = 1 + ∑ j, v j ^ s := by
    rw [Fintype.sum_option]; simp [hu, Real.one_rpow]
  have hcard : (Fintype.card (Option σ) : ℝ) = (Fintype.card σ : ℝ) + 1 := by
    rw [Fintype.card_option]; push_cast; ring
  have h1 : 1 + ∑ j, v j ≤ ((Fintype.card σ : ℝ) + 1) * T := by
    rw [← hsumu, ← hcard]
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Option σ)) u T (fun o _ => hle o)
    simpa [nsmul_eq_mul] using this
  have h2 : T ^ s ≤ 1 + ∑ j, v j ^ s := by
    rw [← hsumus, hT, ho₀]
    exact Finset.single_le_sum (f := fun o => u o ^ s) (fun o _ => Real.rpow_nonneg (hu0 o) s) (Finset.mem_univ o₀)
  have hn : 0 ≤ (Fintype.card σ : ℝ) + 1 := by positivity
  calc (1 + ∑ j, v j) ^ s ≤ (((Fintype.card σ : ℝ) + 1) * T) ^ s :=
        Real.rpow_le_rpow (by have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hv j); linarith) h1 hs
    _ = ((Fintype.card σ : ℝ) + 1) ^ s * T ^ s := Real.mul_rpow hn hT0
    _ ≤ ((Fintype.card σ : ℝ) + 1) ^ s * (1 + ∑ j, v j ^ s) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hn s)

theorem rpow_le_one_add_pow (v : ℝ) (hv : 0 ≤ v) (s : ℝ) (hs : 0 ≤ s) (m : ℕ) (hsm : s ≤ m) :
    v ^ s ≤ 1 + v ^ m := by
  rcases le_or_gt v 1 with h | h
  · exact (Real.rpow_le_one hv h hs).trans (le_add_of_nonneg_right (pow_nonneg hv m))
  · have : v ^ s ≤ v ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le hsm
    rw [Real.rpow_natCast] at this
    linarith

theorem sqrt_sum_sq_toReal_eLpNorm_smul {ι : Type} (Fπ : Finset ι) (ν : Measure (AdelicGL2 (𝓞 K) K))
    (T₁ T₂ : ι → AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) (h : ∀ i ∈ Fπ, T₂ i = c • T₁ i) :
    Real.sqrt (∑ i ∈ Fπ, (eLpNorm (T₂ i) 2 ν).toReal ^ 2) =
      ‖c‖ * Real.sqrt (∑ i ∈ Fπ, (eLpNorm (T₁ i) 2 ν).toReal ^ 2) := by
  have hterm : ∀ i ∈ Fπ, (eLpNorm (T₂ i) 2 ν).toReal ^ 2 = ‖c‖ ^ 2 * (eLpNorm (T₁ i) 2 ν).toReal ^ 2 := by
    intro i hi
    rw [h i hi, eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, mul_pow]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem continuous_archDerivAtComplex_of_mem
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K) (π : HeckeEigensystem K ℂ)
    (b : AdelicGL2 (𝓞 K) K → ℂ)
    (hb : b ∈ isotypicCuspSubmodule K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
    (hbR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchSmoothAt hw b ∧ ∃ lam : ℂ, archCasimirAt hw b = lam • b)
    (hbC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchSmoothAtComplex hw b ∧ ∃ lam lam' : ℂ,
        archCasimirAtComplex hw b = lam • b ∧ archCasimirBarAtComplex hw b = lam' • b)
    (w : InfinitePlace K) (hw : w.IsComplex) :
    (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d b)) ∧
    (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' b))) := by
  have h := AutomorphicForm.forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
    K α β hα hαβ ξK hξc hξt SK N hN tysK π b hb hbR hbC
  exact ⟨fun d => (h [Sum.inr ⟨w, hw, d⟩]).1, fun d d' => (h [Sum.inr ⟨w, hw, d⟩, Sum.inr ⟨w, hw, d'⟩]).1⟩

end DecayHSAssembly

open DecayHSAssembly in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hff : IsFactorizableTestFn K f)
    (hfU : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ M : ℝ, ∀ (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ),
      (∀ i, cls i ∈ cuspClasses K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK ∧
        b i ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK) →
      (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, b i g * conj (b i g)
          ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1) →
      (∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, b i g * conj (b j g)
          ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) →
      ∀ (lamR lamC lamC' : HeckeEigensystem K ℂ → InfinitePlace K → ℂ),
        (∀ (π : HeckeEigensystem K ℂ) (w : InfinitePlace K) (hw : w.IsReal),
          lamC π w = 0 ∧ lamC' π w = 0 ∧
          ∀ b' ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK,
            IsArchSmoothAt hw b' ∧ archCasimirAt hw b' = lamR π w • b') →
        (∀ (π : HeckeEigensystem K ℂ) (w : InfinitePlace K) (hw : w.IsComplex),
          lamR π w = 0 ∧
          ∀ b' ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK,
            IsArchSmoothAtComplex hw b' ∧ archCasimirAtComplex hw b' = lamC π w • b' ∧
              archCasimirBarAtComplex hw b' = lamC' π w • b') →
        ∀ (F : Finset ι) [DecidableEq (HeckeEigensystem K ℂ)],
          ∑ π ∈ F.image cls,
            (1 + ∑ w : InfinitePlace K, (‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖)) ^ s *
              Real.sqrt (∑ i ∈ F.filter (fun i => cls i = π),
                (eLpNorm (convOp K f (b i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
                (AutomorphicForm.canonicalTruncationDomain K α β))).toReal ^ 2) ≤ M := by
  classical

  set U : Subgroup (AdelicGL2 (𝓞 K) K) := principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K with hUdef
  have hU : U ≤ finiteAdelicGL2Subgroup K := inf_le_right
  set m : ℕ := ⌈s⌉₊ with hm
  have hsm : s ≤ (m : ℝ) := Nat.le_ceil s

  have hRit := fun (w : InfinitePlace K) (hw : w.IsReal) =>
    DecayHSAssembly.exists_iterate_shift_real w hw U hU f hff hfU m
  have hCit := fun (w : InfinitePlace K) (hw : w.IsComplex) =>
    DecayHSAssembly.exists_iterate_shift_complex w hw U hU f hff hfU m
  have hCbit := fun (w : InfinitePlace K) (hw : w.IsComplex) =>
    DecayHSAssembly.exists_iterate_shift_complex_bar w hw U hU f hff hfU m
  choose βR hβR hβRU hβRk using hRit
  choose βC hβC hβCU hβCk using hCit
  choose βCb hβCb hβCbU hβCbk using hCbit
  let g : InfinitePlace K ⊕ InfinitePlace K ⊕ InfinitePlace K → (AdelicGL2 (𝓞 K) K → ℂ) := fun σ =>
    Sum.elim (fun w => if hw : w.IsReal then βR w hw else f)
      (Sum.elim (fun w => if hw : w.IsComplex then βC w hw else f)
        (fun w => if hw : w.IsComplex then βCb w hw else f)) σ
  have hg : ∀ σ, IsFactorizableTestFn K (g σ) ∧ IsBiInvariantUnder K U (g σ) := by
    rintro (w | w | w) <;> simp only [g, Sum.elim_inl, Sum.elim_inr] <;> split_ifs
    · exact ⟨hβR _ _, hβRU _ _⟩
    · exact ⟨hff, hfU⟩
    · exact ⟨hβC _ _, hβCU _ _⟩
    · exact ⟨hff, hfU⟩
    · exact ⟨hβCb _ _, hβCbU _ _⟩
    · exact ⟨hff, hfU⟩

  have hHS0 : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ), IsFactorizableTestFn K φ → IsBiInvariantUnder K U φ →
      ∃ M : ℝ, ∀ (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ),
        (∀ i, cls i ∈ cuspClasses K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK) →
        (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, b i g * conj (b i g)
            ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1) →
        (∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, b i g * conj (b j g)
            ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) →
        ∀ (F : Finset ι) [DecidableEq (HeckeEigensystem K ℂ)],
          ∑ π ∈ F.image cls,
            Real.sqrt (∑ i ∈ F.filter (fun i => cls i = π),
              (eLpNorm (convOp K φ (b i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
                (AutomorphicForm.canonicalTruncationDomain K α β))).toReal ^ 2) ≤ M := by
    intro φ hφ hφU
    obtain ⟨hφc, hφs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K φ hφ
    exact AutomorphicForm.exists_forall_sum_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal
      K α β hα hαβ ξK hξc hξt SK N hN tysK φ hφc hφs hφ hφU
  obtain ⟨M₀, hM₀⟩ := hHS0 f hff hfU
  choose Mσ hMσ using fun σ => hHS0 (g σ) (hg σ).1 (hg σ).2
  set n : ℕ := Fintype.card (InfinitePlace K ⊕ InfinitePlace K ⊕ InfinitePlace K) with hn
  set Cn : ℝ := ((n : ℝ) + 1) ^ s with hCn
  have hCn0 : 0 ≤ Cn := Real.rpow_nonneg (by positivity) s
  refine ⟨Cn * (((n : ℝ) + 1) * M₀ + ∑ σ, Mσ σ), ?_⟩
  intro ι b cls hb hb₁ hb₀ lamR lamC lamC' hR hC F _inst

  let HS : (AdelicGL2 (𝓞 K) K → ℂ) → HeckeEigensystem K ℂ → ℝ := fun φ π =>
    Real.sqrt (∑ i ∈ F.filter (fun i => cls i = π), (eLpNorm (convOp K φ (b i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
                (AutomorphicForm.canonicalTruncationDomain K α β))).toReal ^ 2)
  have hHSnn : ∀ φ π, 0 ≤ HS φ π := fun _ _ => Real.sqrt_nonneg _
  let v : HeckeEigensystem K ℂ → InfinitePlace K ⊕ InfinitePlace K ⊕ InfinitePlace K → ℝ := fun π σ =>
    Sum.elim (fun w => ‖lamR π w‖) (Sum.elim (fun w => ‖lamC π w‖) (fun w => ‖lamC' π w‖)) σ
  have hv0 : ∀ π σ, 0 ≤ v π σ := by
    rintro π (w | w | w) <;> exact norm_nonneg _
  have hvsum : ∀ π, ∑ σ, v π σ = ∑ w : InfinitePlace K, (‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖) := by
    intro π
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [v, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
    ring
  have hslot : ∀ π ∈ F.image cls, ∀ σ, (v π σ) ^ s * HS f π ≤ HS f π + HS (g σ) π := by
    intro π hπ σ
    have hmem : ∀ i ∈ F.filter (fun i => cls i = π), b i ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK := fun i hi => by
      have := (hb i).2
      rwa [(Finset.mem_filter.1 hi).2] at this
    have hcont : ∀ i ∈ F.filter (fun i => cls i = π), Continuous (b i) := fun i hi =>
      continuous_of_mem_isotypicCuspSubmodule (Submodule.mem_inf.1 (hmem i hi)).1
    have step1 : (v π σ) ^ s * HS f π ≤ HS f π + (v π σ) ^ m * HS f π := by
      have := DecayHSAssembly.rpow_le_one_add_pow (v π σ) (hv0 π σ) s hs m hsm
      nlinarith [hHSnn f π, this]
    refine step1.trans (add_le_add le_rfl ?_)
    have zero_case : ∀ (u : ℝ), u = 0 → u ^ m * HS f π ≤ HS f π := fun u hu => by
      subst hu
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0, pow_zero, one_mul]
      · rw [zero_pow hpos.ne', zero_mul]; exact hHSnn f π
    have hregC : ∀ (w : InfinitePlace K) (hwc : w.IsComplex), ∀ i ∈ F.filter (fun i => cls i = π),
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hwc d (b i))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hwc d (archDerivAtComplex hwc d' (b i)))) :=
      fun w hwc i hi => DecayHSAssembly.continuous_archDerivAtComplex_of_mem α β hα hαβ ξK hξc hξt SK N hN tysK π (b i)
        (hmem i hi)
        (fun w' hw' => ⟨((hR π w' hw').2.2 (b i) (hmem i hi)).1, lamR π w', ((hR π w' hw').2.2 (b i) (hmem i hi)).2⟩)
        (fun w' hw' => ⟨((hC π w' hw').2 (b i) (hmem i hi)).1, lamC π w', lamC' π w',
          ((hC π w' hw').2 (b i) (hmem i hi)).2.1, ((hC π w' hw').2 (b i) (hmem i hi)).2.2⟩) w hwc
    rcases σ with w | w | w
    ·
      change ‖lamR π w‖ ^ m * HS f π ≤ HS (if hw : w.IsReal then βR w hw else f) π
      by_cases hw : w.IsReal
      · rw [dif_pos hw]
        simp only [HS]
        rw [DecayHSAssembly.sqrt_sum_sq_toReal_eLpNorm_smul _ _ (fun i => convOp K f (b i))
          (fun i => convOp K (βR w hw) (b i)) ((lamR π w) ^ m) (fun i hi =>
            hβRk w hw (b i) (hcont i hi) ((hR π w hw).2.2 (b i) (hmem i hi)).1 (lamR π w)
              ((hR π w hw).2.2 (b i) (hmem i hi)).2), norm_pow]
      · rw [dif_neg hw]
        exact zero_case _ (by rw [(hC π w (InfinitePlace.not_isReal_iff_isComplex.1 hw)).1, norm_zero])
    ·
      change ‖lamC π w‖ ^ m * HS f π ≤ HS (if hw : w.IsComplex then βC w hw else f) π
      by_cases hw : w.IsComplex
      · rw [dif_pos hw]
        simp only [HS]
        rw [DecayHSAssembly.sqrt_sum_sq_toReal_eLpNorm_smul _ _ (fun i => convOp K f (b i))
          (fun i => convOp K (βC w hw) (b i)) ((lamC π w) ^ m) (fun i hi =>
            hβCk w hw (b i) (hcont i hi) ((hC π w hw).2 (b i) (hmem i hi)).1 (hregC w hw i hi).1 (hregC w hw i hi).2
              (lamC π w) (lamC' π w) ((hC π w hw).2 (b i) (hmem i hi)).2.1 ((hC π w hw).2 (b i) (hmem i hi)).2.2),
          norm_pow]
      · rw [dif_neg hw]
        exact zero_case _ (by rw [(hR π w (InfinitePlace.not_isComplex_iff_isReal.1 hw)).1, norm_zero])
    ·
      change ‖lamC' π w‖ ^ m * HS f π ≤ HS (if hw : w.IsComplex then βCb w hw else f) π
      by_cases hw : w.IsComplex
      · rw [dif_pos hw]
        simp only [HS]
        rw [DecayHSAssembly.sqrt_sum_sq_toReal_eLpNorm_smul _ _ (fun i => convOp K f (b i))
          (fun i => convOp K (βCb w hw) (b i)) ((lamC' π w) ^ m) (fun i hi =>
            hβCbk w hw (b i) (hcont i hi) ((hC π w hw).2 (b i) (hmem i hi)).1 (hregC w hw i hi).1 (hregC w hw i hi).2
              (lamC π w) (lamC' π w) ((hC π w hw).2 (b i) (hmem i hi)).2.1 ((hC π w hw).2 (b i) (hmem i hi)).2.2),
          norm_pow]
      · rw [dif_neg hw]
        exact zero_case _ (by rw [(hR π w (InfinitePlace.not_isComplex_iff_isReal.1 hw)).2.1, norm_zero])
  have hkey : ∀ π ∈ F.image cls,
      (1 + ∑ w : InfinitePlace K, (‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖)) ^ s * HS f π ≤
        Cn * (((n : ℝ) + 1) * HS f π + ∑ σ, HS (g σ) π) := by
    intro π hπ
    rw [← hvsum π]
    have h1 := DecayHSAssembly.one_add_sum_rpow_le (v π) (hv0 π) s hs
    calc (1 + ∑ σ, v π σ) ^ s * HS f π ≤ (Cn * (1 + ∑ σ, v π σ ^ s)) * HS f π :=
          mul_le_mul_of_nonneg_right (by simpa only [hCn, hn] using h1) (hHSnn f π)
      _ = Cn * (HS f π + ∑ σ, v π σ ^ s * HS f π) := by
          have e : (1 + ∑ σ, v π σ ^ s) * HS f π = HS f π + ∑ σ, v π σ ^ s * HS f π := by
            rw [add_mul, one_mul, Finset.sum_mul]
          rw [mul_assoc, e]
      _ ≤ Cn * (HS f π + ∑ σ, (HS f π + HS (g σ) π)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCn0
          exact add_le_add le_rfl (Finset.sum_le_sum fun σ _ => hslot π hπ σ)
      _ = Cn * (((n : ℝ) + 1) * HS f π + ∑ σ, HS (g σ) π) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← hn, nsmul_eq_mul]
          ring

  calc ∑ π ∈ F.image cls, (1 + ∑ w : InfinitePlace K, (‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖)) ^ s * HS f π
      ≤ ∑ π ∈ F.image cls, Cn * (((n : ℝ) + 1) * HS f π + ∑ σ, HS (g σ) π) := Finset.sum_le_sum hkey
    _ = Cn * (((n : ℝ) + 1) * ∑ π ∈ F.image cls, HS f π + ∑ σ, ∑ π ∈ F.image cls, HS (g σ) π) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_comm]
    _ ≤ Cn * (((n : ℝ) + 1) * M₀ + ∑ σ, Mσ σ) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hCn0
        · exact mul_le_mul_of_nonneg_left (hM₀ ι b cls hb hb₁ hb₀ F) (by positivity)
        · exact Finset.sum_le_sum fun σ _ => hMσ σ ι b cls hb hb₁ hb₀ F

#print axioms solution

end
end S_AutomorphicForm_exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul (solution)
