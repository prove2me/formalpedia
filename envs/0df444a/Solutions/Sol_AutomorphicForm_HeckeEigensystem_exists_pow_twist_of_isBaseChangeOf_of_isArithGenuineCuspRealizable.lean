-- Prove2me | solution 1 for AutomorphicForm.HeckeEigensystem.exists_pow_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6efb54f4-8bd2-5db8-a512-1ff13f0dcea5

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.RamificationInertia.Basic
import Theorems.Thm_AutomorphicForm_exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_self_and_meromorphicOrderAt_one_neg
import Theorems.Thm_AutomorphicForm_exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_of_meromorphicOrderAt_one_neg
import Theorems.Thm_AutomorphicForm_exists_isArithGenuineCuspRealizable_rayClassChar_twist_of_coversModCentre
import Theorems.Thm_AutomorphicForm_HeckeEigensystem_hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf
import Theorems.Thm_AutomorphicForm_coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_MeromorphicAt_exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_HeckeEigensystem_exists_pow_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_zero UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def"
p2m_attr_erase "simp" "TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply
open scoped Classical

noncomputable section

namespace RS9H

abbrev rsFactor {K : Type} [Field K] [NumberField K] (σ τ : HeckeEigensystem K ℂ)
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v / σ.b v) (σ.b v)⁻¹ (τ.a v) (τ.b v) 0).eval
    (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹

abbrev chiPow {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) (η : NarrowRayClassGroup F 𝔣 →* ℂˣ)
    (i : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if hv : ¬ v.asIdeal ∣ 𝔣 then (((η ^ i) (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) else 0

theorem norm_rayClassChar_apply_eq_one {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup F 𝔣 →* ℂˣ) (g : NarrowRayClassGroup F 𝔣) : ‖((χ g : ℂˣ) : ℂ)‖ = 1 := by
  haveI : Finite (NarrowRayClassGroup F 𝔣) := Deep.NTSupply.finite F h𝔣
  have hfin : IsOfFinOrder (χ g) := MonoidHom.isOfFinOrder χ (isOfFinOrder_of_finite g)
  obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
  have : ((χ g : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one this hn.ne'

theorem norm_chiPow_eq_one {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F))
    (η : NarrowRayClassGroup F 𝔣 →* ℂˣ) (i : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    ‖chiPow 𝔣 η i v‖ = 1 := by
  have h𝔣 : 𝔣 ≠ ⊥ := by
    rintro rfl
    exact hv (by rw [← Ideal.zero_eq_bot]; exact dvd_zero _)
  haveI : Finite (NarrowRayClassGroup F 𝔣) := Deep.NTSupply.finite F h𝔣
  simp only [chiPow, dif_pos hv]
  set g := primeClass F 𝔣 v hv
  have hfin : IsOfFinOrder ((η ^ i) g) := MonoidHom.isOfFinOrder (η ^ i) (isOfFinOrder_of_finite g)
  obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
  have : (((η ^ i) g : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one this hn.ne'

theorem G0_d₂_pos (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) : 0 < d₂ := by
  by_contra hle
  push Not at hle
  obtain ⟨γ, z, hmem⟩ := hcov 1
  simp only [Set.mem_iUnion, Set.mem_image] at hmem
  obtain ⟨x, -, g, hg, -⟩ := hmem
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have h1 := ((mem_centreCutSiegelSet_iff).mp hg).2.2.2 w₀
  have h2 := NumberField.AdelicVolume.archDetNorm_pos w₀ g
  linarith [h1.2]

theorem meromorphicOrderAt_one_eq_of_eqOn_halfPlane (f g : ℂ → ℂ) (a : ℝ) (ha : a < 1) (σ₀ : ℝ)
    (hf : MeromorphicOn f {s : ℂ | a < s.re}) (hg : MeromorphicOn g {s : ℂ | a < s.re})
    (h : ∀ s : ℂ, σ₀ < s.re → f s = g s) : meromorphicOrderAt f 1 = meromorphicOrderAt g 1 := by
  set U : Set ℂ := {s : ℂ | a < s.re} with hU
  set d : ℂ → ℂ := fun z => f z - g z with hd
  have hdm : MeromorphicOn d U := hf.sub hg
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt a).isPreconnected

  set x₀ : ℂ := ((max σ₀ 1 + 1 : ℝ) : ℂ) with hx₀
  have hx₀re : x₀.re = max σ₀ 1 + 1 := by simp [hx₀]
  have hx₀U : x₀ ∈ U := by
    show a < x₀.re
    rw [hx₀re]
    linarith [le_max_right σ₀ 1]
  have h1U : (1 : ℂ) ∈ U := by show a < (1 : ℂ).re; simp; exact ha
  have hx₀top : meromorphicOrderAt d x₀ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hopen : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : x₀ ∈ {s : ℂ | σ₀ < s.re} := by
      show σ₀ < x₀.re
      rw [hx₀re]
      linarith [le_max_left σ₀ 1]
    exact eventually_nhdsWithin_of_eventually_nhds
      (Filter.eventually_of_mem (hopen.mem_nhds hmem) fun z hz => by simp only [hd, h z hz, sub_self])
  have h1top : meromorphicOrderAt d 1 = ⊤ := by
    by_contra hne
    exact (hdm.meromorphicOrderAt_ne_top_of_isPreconnected hUpre h1U hx₀U hne) hx₀top
  rw [meromorphicOrderAt_eq_top_iff] at h1top
  exact meromorphicOrderAt_congr (h1top.mono fun z hz => sub_eq_zero.mp hz)

theorem exists_finset_over (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (SF : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ SE : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ SF := by
  have hfin : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ SF}.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion SF.finite_toSet fun v _ =>
      Ideal.finite_factors (I := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))) ?_) ?_
    · rw [Ideal.zero_eq_bot, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
      exact v.ne_bot
    · intro w hw
      simp only [Set.mem_setOf_eq] at hw
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe]
      refine ⟨w.under (𝓞 F), hw, ?_⟩
      rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
      exact le_of_eq rfl
  exact ⟨hfin.toFinset, fun w => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩

theorem exists_forall_pow_b_eq_of_isBaseChangeOf
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {R : Type*} [CommRing R]
    (π π' : HeckeEigensystem F R) (Ψ : HeckeEigensystem E R)
    (h : IsBaseChangeOf π Ψ) (h' : IsBaseChangeOf π' Ψ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      ∃ f : ℕ, 0 < f ∧ π'.b v ^ f = π.b v ^ f := by
  classical
  obtain ⟨SE, hSE⟩ := h
  obtain ⟨SE', hSE'⟩ := h'
  refine ⟨(SE ∪ SE').image (fun w => w.under (𝓞 F)), fun v hv => ?_⟩
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let w : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, hQne⟩
  have hwv : w.under (𝓞 F) = v := by
    ext1
    exact hQover.over.symm
  have hw : w ∉ SE ∪ SE' := by
    intro hmem
    exact hv (Finset.mem_image.mpr ⟨w, hmem, hwv⟩)
  obtain ⟨-, hb⟩ := hSE w (fun hm => hw (Finset.mem_union_left _ hm))
  obtain ⟨-, hb'⟩ := hSE' w (fun hm => hw (Finset.mem_union_right _ hm))
  refine ⟨(w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal, ?_, ?_⟩
  · rw [hwv]
    haveI : w.asIdeal.LiesOver v.asIdeal := hQover
    exact Ideal.inertiaDeg'_pos v.asIdeal w.asIdeal
  · rw [hwv] at hb hb' ⊢
    rw [← hb, ← hb']

end RS9H

open RS9H in
theorem solution
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (cF uF d₁F d₂F : ℝ) (TF : Finset (AdelicGL2 (𝓞 F) F))
    (hd₁F : 0 < d₁F) (hdF : d₁F < d₂F)
    (hcovF : CoversModCentre F (⋃ x ∈ TF, (· * x) '' centreCutSiegelSet F cF uF d₁F d₂F))
    (cE uE d₁E d₂E : ℝ) (TE : Finset (AdelicGL2 (𝓞 E) E))
    (hdE : d₁E < d₂E)
    (hcovE : CoversModCentre E (⋃ x ∈ TE, (· * x) '' centreCutSiegelSet E cE uE d₁E d₂E))
    (𝔣 : Ideal (𝓞 F)) (η : NarrowRayClassGroup F 𝔣 →* ℂˣ)
    (hη : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ ((w.under (𝓞 F)).asIdeal ∣ 𝔣)),
      orderOf (η (primeClass F 𝔣 (w.under (𝓞 F)) hw)) =
        (w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal)
    (π π' : HeckeEigensystem F ℂ) (Ψ : HeckeEigensystem E ℂ)
    (hπ : IsArithGenuineCuspRealizable F
      (productionPinsOf F (⋃ x ∈ TF, (· * x) '' centreCutSiegelSet F cF uF d₁F d₂F)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) π)
    (hπ' : IsArithGenuineCuspRealizable F
      (productionPinsOf F (⋃ x ∈ TF, (· * x) '' centreCutSiegelSet F cF uF d₁F d₂F)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) π')
    (hΨ : IsArithGenuineCuspRealizable E
      (productionPinsOf E (⋃ x ∈ TE, (· * x) '' centreCutSiegelSet E cE uE d₁E d₂E)
        (fun N => levelOne (𝓞 E) E N ⊓ finiteAdelicGL2Subgroup E) (fun v => heckeGen (𝓞 E) E v)
        (adelicBox E)) Ψ)
    (h : IsBaseChangeOf π Ψ) (h' : IsBaseChangeOf π' Ψ) :
    ∃ i < Module.finrank F E, ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ v ∉ S, ∀ (hv : ¬ v.asIdeal ∣ 𝔣),
        π'.a v = ((η ^ i) (primeClass F 𝔣 v hv) : ℂ) * π.a v ∧
        π'.b v = ((η ^ i) (primeClass F 𝔣 v hv) : ℂ) ^ 2 * π.b v := by
  set m := Module.finrank F E with hm

  by_cases h𝔣 : 𝔣 = ⊥
  · haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    refine ⟨0, Module.finrank_pos, ∅, fun v _ hv => absurd ?_ hv⟩
    rw [h𝔣, ← Ideal.zero_eq_bot]
    exact dvd_zero _

  have hcF : 0 < cF := by
    by_contra hle
    push Not at hle
    exact AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
      F cF uF d₁F d₂F TF hle hdF hcovF π hπ
  have hcE : 0 < cE := by
    by_contra hle
    push Not at hle
    exact AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
      E cE uE d₁E d₂E TE hle hdE hcovE Ψ hΨ
  have hd₂E : 0 < d₂E := G0_d₂_pos E cE uE d₁E d₂E TE hcovE
  set d₁E' : ℝ := max d₁E (d₂E / 2) with hd₁E'
  have hle : d₁E ≤ d₁E' := le_max_left _ _
  have hlt : d₁E' < d₂E := max_lt hdE (by linarith)
  have hd₁E'pos : 0 < d₁E' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨hcovE', hΨ'⟩ :=
    AutomorphicForm.coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre
      E cE uE d₁E d₂E d₁E' TE hle hlt hcovE Ψ hΨ

  obtain ⟨S₁E, hPOLE⟩ := AutomorphicForm.exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_self_and_meromorphicOrderAt_one_neg E cE uE d₁E' d₂E TE hcE hd₁E'pos hlt hcovE' Ψ hΨ'

  have hG2 : ∀ i : Fin m, ∃ πt : HeckeEigensystem F ℂ, ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      (∀ v ∉ S, ∀ (hv : ¬ v.asIdeal ∣ 𝔣),
        πt.a v = ((η ^ (i : ℕ)) (primeClass F 𝔣 v hv) : ℂ) * π.a v ∧
        πt.b v = ((η ^ (i : ℕ)) (primeClass F 𝔣 v hv) : ℂ) ^ 2 * π.b v) ∧
      IsArithGenuineCuspRealizable F
        (productionPinsOf F (⋃ x ∈ TF, (· * x) '' centreCutSiegelSet F cF uF d₁F d₂F)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) πt :=
    fun i => AutomorphicForm.exists_isArithGenuineCuspRealizable_rayClassChar_twist_of_coversModCentre F cF uF d₁F d₂F TF hcF hd₁F hdF hcovF 𝔣 h𝔣 (η ^ (i : ℕ)) π hπ
  choose πt St hSt hπt using hG2

  have hunit : ∀ i : Fin m, ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ‖(πt i).b v‖ = ‖π'.b v‖ := by
    intro i
    obtain ⟨S, hS⟩ := exists_forall_pow_b_eq_of_isBaseChangeOf F E π π' Ψ h h'
    refine ⟨S ∪ St i ∪ (Ideal.finite_factors h𝔣).toFinset, fun v hv => ?_⟩
    simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
    obtain ⟨⟨hvS, hvSt⟩, hvf⟩ := hv
    obtain ⟨f, hf, hpow⟩ := hS v hvS
    have hn : ‖π'.b v‖ = ‖π.b v‖ := by
      have := congrArg (fun z : ℂ => ‖z‖) hpow
      simp only [norm_pow] at this
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hf.ne').mp this
    rw [(hSt i v hvSt hvf).2, norm_mul, norm_pow, norm_rayClassChar_apply_eq_one 𝔣 h𝔣, one_pow, one_mul, hn]

  have hMERO : ∀ i : Fin m, ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₁ ⊆ S →
      ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => rsFactor (πt i) π' v.1 s) (Λ s)) ∧
      (meromorphicOrderAt Λ 1 < 0 → HeckeEigensystem.AgreesAwayFromFinite π' (πt i)) :=
    fun i => AutomorphicForm.exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_of_meromorphicOrderAt_one_neg F cF uF d₁F d₂F TF hcF hd₁F hdF hcovF (πt i) π' (hπt i) hπ' (hunit i)
  choose S₁F hS₁F using hMERO

  obtain ⟨S₂, hS₂⟩ := AutomorphicForm.HeckeEigensystem.hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf F E 𝔣 h𝔣 η hη π π' Ψ h h'
  set SF : Finset (HeightOneSpectrum (𝓞 F)) :=
    S₂ ∪ Finset.univ.biUnion S₁F ∪ S₁E.image (fun w => w.under (𝓞 F)) ∪ Finset.univ.biUnion St ∪
      (Ideal.finite_factors h𝔣).toFinset with hSF
  obtain ⟨SE, hSE⟩ := exists_finset_over F E SF
  have hS₁E : S₁E ⊆ SE := fun w hw =>
    (hSE w).mpr (by
      rw [hSF]
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))))
  have hS₂SF : S₂ ⊆ SF := fun v hv => by
    rw [hSF]
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hv)))
  have hS₁FSF : ∀ i : Fin m, S₁F i ⊆ SF := fun i v hv => by
    rw [hSF]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hv⟩))))
  have hStSF : ∀ i : Fin m, ∀ v ∉ SF, v ∉ St i ∧ ¬ v.asIdeal ∣ 𝔣 := fun i v hv => by
    constructor
    · intro h1; apply hv; rw [hSF]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h1⟩))
    · intro h1; apply hv; rw [hSF]
      exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h1)
  obtain ⟨σE, ΛE, ⟨aE, haE, hΛEmero⟩, hΛEpole, hΛEprod⟩ := hPOLE SE hS₁E
  have hF : ∀ i : Fin m, ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ SF} => rsFactor (πt i) π' v.1 s) (Λ s)) ∧
      (meromorphicOrderAt Λ 1 < 0 → HeckeEigensystem.AgreesAwayFromFinite π' (πt i)) :=
    fun i => hS₁F i SF (hS₁FSF i)
  choose σF Λ hΛmero₀ hΛprod hΛimp using hF
  choose aF haF hΛmeroF using hΛmero₀

  have htab : ∀ (i : Fin m) (s : ℂ),
      (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ SF} => rsFactor (πt i) π' v.1 s) =
        fun v => rsFactor (π.twist (chiPow 𝔣 η i)) π' v.1 s := by
    intro i s
    funext v
    obtain ⟨hvSt, hvf⟩ := hStSF i v.1 v.2
    obtain ⟨ha, hb⟩ := hSt i v.1 hvSt hvf
    simp only [rsFactor, HeckeEigensystem.twist_a, HeckeEigensystem.twist_b, chiPow, dif_pos hvf, ha, hb]

  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Nonempty (Fin m) := ⟨⟨0, Module.finrank_pos⟩⟩
  set σ₁ : ℝ := max σE (Finset.univ.sup' Finset.univ_nonempty σF) with hσ₁def
  have hσ₁ : ∀ s : ℂ, σ₁ < s.re → ΛE s = ∏ i : Fin m, Λ i s := by
    intro s hs
    refine hS₂ SF hS₂SF SE hSE s (ΛE s) (fun i => Λ i s) (hΛEprod s ?_) (fun i => ?_)
    · exact lt_of_le_of_lt (le_max_left _ _) hs
    · rw [← htab i s]
      exact hΛprod i s (lt_of_le_of_lt ((Finset.le_sup' σF (Finset.mem_univ i)).trans (le_max_right _ _)) hs)

  set a₁ : ℝ := max aE (Finset.univ.sup' Finset.univ_nonempty aF) with ha₁def
  have ha₁ : a₁ < 1 := max_lt haE ((Finset.sup'_lt_iff Finset.univ_nonempty).mpr fun j _ => haF j)
  have hmonoE : {s : ℂ | a₁ < s.re} ⊆ {s : ℂ | aE < s.re} := fun s (hs : a₁ < s.re) =>
    show aE < s.re from lt_of_le_of_lt (le_max_left _ _) hs
  have hmonoF : ∀ j : Fin m, {s : ℂ | a₁ < s.re} ⊆ {s : ℂ | aF j < s.re} := fun j s (hs : a₁ < s.re) =>
    show aF j < s.re from lt_of_le_of_lt ((Finset.le_sup' aF (Finset.mem_univ j)).trans (le_max_right _ _)) hs
  have hΛEmero' : MeromorphicOn ΛE {s : ℂ | a₁ < s.re} := hΛEmero.mono_set hmonoE
  have hΛmero : ∀ j : Fin m, MeromorphicOn (Λ j) {s : ℂ | a₁ < s.re} := fun j => (hΛmeroF j).mono_set (hmonoF j)

  set P : ℂ → ℂ := fun s => ∏ i : Fin m, Λ i s with hP
  have hPmero : MeromorphicOn P {s : ℂ | a₁ < s.re} :=
    MeromorphicOn.fun_prod (fun j _ => hΛmero j)
  have hPorder : meromorphicOrderAt P 1 < 0 := by
    rw [← meromorphicOrderAt_one_eq_of_eqOn_halfPlane ΛE P a₁ ha₁ σ₁ hΛEmero' hPmero hσ₁]
    exact hΛEpole

  have hone : (1 : ℂ) ∈ {s : ℂ | a₁ < s.re} := by simp; exact ha₁
  obtain ⟨i, -, hi⟩ := MeromorphicAt.exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod
    (s := (Finset.univ : Finset (Fin m))) (t := (∅ : Finset Unit)) (f := Λ) (p := P) (h := fun _ => fun _ => (1 : ℂ))
    (x := (1 : ℂ)) (fun j _ => hΛmero j 1 hone) (hPmero 1 hone) hPorder (fun _ hj => by simp at hj) (fun _ hj => by simp at hj)
    (Filter.Eventually.of_forall fun z => by simp [hP])

  obtain ⟨S, hS⟩ := hΛimp i hi
  refine ⟨i, i.isLt, S ∪ St i, fun v hv hfv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  obtain ⟨ha, hb⟩ := hS v hv.1
  obtain ⟨ha', hb'⟩ := hSt i v hv.2 hfv
  exact ⟨ha.trans ha', hb.trans hb'⟩

end

end S_AutomorphicForm_HeckeEigensystem_exists_pow_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable
end P2MW
export P2MW.S_AutomorphicForm_HeckeEigensystem_exists_pow_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable (solution)
