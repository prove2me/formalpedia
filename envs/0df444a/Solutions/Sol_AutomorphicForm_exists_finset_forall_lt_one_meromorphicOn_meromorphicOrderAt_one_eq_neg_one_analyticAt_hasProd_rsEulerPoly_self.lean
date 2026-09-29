-- Prove2me | solution 1 for AutomorphicForm.exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/34939936-6285-50cc-a69f-db0db1eb28bd

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Theorems.Thm_AutomorphicForm_exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1"
p2m_attr_erase "simp" "AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units"
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

namespace RS40M

open Polynomial Filter Topology

variable {K : Type} [Field K] [NumberField K]

abbrev locPoly (Θ : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) : ℂ[X] :=
  LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v / Θ.b v) (Θ.b v)⁻¹ (Θ.a v) (Θ.b v) 0

abbrev locEval (Θ : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  (locPoly Θ v).eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))

theorem absNorm_ne_zero (v : HeightOneSpectrum (𝓞 K)) : Ideal.absNorm v.asIdeal ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 := absNorm_ne_zero v
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem rsEulerPoly_coeff_zero {R : Type*} [CommRing R] (a b e₁ e₂ e₃ : R) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly a b e₁ e₂ e₃).coeff 0 = 1 := by
  simp [LanglandsTunnell.RankinSelberg.rsEulerPoly, coeff_one, coeff_X, coeff_C, coeff_X_pow]

theorem exists_forall_eval_cpow_neg_ne_zero (P : ℂ[X]) (hP : P.coeff 0 = 1) (N : ℕ) (hN : 2 ≤ N) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → P.eval (((N : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
  have h0 : P.eval 0 = 1 := by rw [← coeff_zero_eq_eval_zero]; exact hP
  have hcont : ContinuousAt (fun x : ℂ => P.eval x) 0 := P.continuous.continuousAt
  obtain ⟨δ, hδ, hδP⟩ := (Metric.continuousAt_iff.mp hcont) (1 / 2) (by norm_num)
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans zero_lt_one hNr
  refine ⟨Real.logb N (1 / δ), fun s hs => ?_⟩
  have hsmall : ‖((N : ℕ) : ℂ) ^ (-s)‖ < δ := by
    rw [Complex.norm_natCast_cpow_of_pos (lt_of_lt_of_le (by norm_num) hN), Complex.neg_re]
    calc (N : ℝ) ^ (-s.re) < (N : ℝ) ^ (-Real.logb N (1 / δ)) :=
          Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith)
      _ = δ := by
          rw [Real.rpow_neg hNpos.le, Real.rpow_logb hNpos hNr.ne' (by positivity), one_div, inv_inv]
  intro hzero
  have := hδP (x := ((N : ℕ) : ℂ) ^ (-s)) (by simpa [dist_zero_right] using hsmall)
  rw [hzero, h0, dist_eq_norm] at this
  norm_num at this

theorem differentiable_locEval (Θ : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    Differentiable ℂ (locEval Θ v) := by
  have hN : (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (absNorm_ne_zero v)
  have h : (fun s : ℂ => (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) =
      fun s => Complex.exp (Complex.log (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * (-s)) := by
    funext s; rw [Complex.cpow_def_of_ne_zero hN]
  have hd : Differentiable ℂ (fun s : ℂ => (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) := by
    rw [h]; fun_prop
  exact (locPoly Θ v).differentiable.comp hd

theorem hasProd_subtype_notMem_of_subset {β : Type*} (f : β → ℂ) {S T : Finset β} (hST : S ⊆ T)
    {a : ℂ} (h : HasProd (fun x : {x // x ∉ S} => f x) a) (hf : ∀ b ∈ T \ S, f b ≠ 0) :
    HasProd (fun x : {x // x ∉ T} => f x) (a * ∏ b ∈ T \ S, (f b)⁻¹) := by
  classical

  have h1 : HasProd (({x | x ∉ S} : Set β).mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := ({x | x ∉ S} : Set β)) (f := f)).mp h

  have h2 : HasProd (((↑(T \ S) : Set β)).mulIndicator fun x => (f x)⁻¹) (∏ b ∈ T \ S, (f b)⁻¹) :=
    (hasProd_subtype_iff_mulIndicator (s := ((↑(T \ S) : Set β))) (f := fun x => (f x)⁻¹)).mp
      (Finset.hasProd (T \ S) fun x => (f x)⁻¹)
  have h3 := h1.mul h2

  have hpt : (fun x => ({x | x ∉ S} : Set β).mulIndicator f x *
      ((↑(T \ S) : Set β)).mulIndicator (fun x => (f x)⁻¹) x) = ({x | x ∉ T} : Set β).mulIndicator f := by
    funext x
    by_cases hxT : x ∈ T
    · by_cases hxS : x ∈ S
      · have h1' : x ∉ ({x | x ∉ S} : Set β) := fun h => h hxS
        have h2' : x ∉ ((↑(T \ S) : Set β)) := by
          rw [Finset.mem_coe, Finset.mem_sdiff]; exact fun h => h.2 hxS
        have h3' : x ∉ ({x | x ∉ T} : Set β) := fun h => h hxT
        rw [Set.mulIndicator_of_notMem h1', Set.mulIndicator_of_notMem h2', Set.mulIndicator_of_notMem h3',
          one_mul]
      · have h1' : x ∈ ({x | x ∉ S} : Set β) := hxS
        have h2' : x ∈ ((↑(T \ S) : Set β)) := by
          rw [Finset.mem_coe, Finset.mem_sdiff]; exact ⟨hxT, hxS⟩
        have h3' : x ∉ ({x | x ∉ T} : Set β) := fun h => h hxT
        rw [Set.mulIndicator_of_mem h1', Set.mulIndicator_of_mem h2', Set.mulIndicator_of_notMem h3',
          mul_inv_cancel₀ (hf x (Finset.mem_sdiff.mpr ⟨hxT, hxS⟩))]
    · have hxS : x ∉ S := fun h => hxT (hST h)
      have h1' : x ∈ ({x | x ∉ S} : Set β) := hxS
      have h2' : x ∉ ((↑(T \ S) : Set β)) := by
        rw [Finset.mem_coe, Finset.mem_sdiff]; exact fun h => hxT h.1
      have h3' : x ∈ ({x | x ∉ T} : Set β) := hxT
      rw [Set.mulIndicator_of_mem h1', Set.mulIndicator_of_notMem h2', Set.mulIndicator_of_mem h3', mul_one]
  rw [hpt] at h3
  exact (hasProd_subtype_iff_mulIndicator (s := ({x | x ∉ T} : Set β)) (f := f)).mpr h3

theorem pole_of_pole0
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S →
      ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      meromorphicOrderAt Λ 1 = -1 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} => (locEval Θ v.1 s)⁻¹) (Λ s) := by
  obtain ⟨S, σ₀, Λ, ⟨a, ha, hmero⟩, hord, han, hprod, hgen⟩ :=
    AutomorphicForm.exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self K c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ
  have hprod' : ∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} => (locEval Θ v.1 s)⁻¹) (Λ s) := hprod
  refine ⟨S, fun S' hSS' => ?_⟩

  have hσv : ∀ v : HeightOneSpectrum (𝓞 K), ∃ σv : ℝ, ∀ s : ℂ, σv < s.re → locEval Θ v s ≠ 0 :=
    fun v => exists_forall_eval_cpow_neg_ne_zero (locPoly Θ v) (rsEulerPoly_coeff_zero _ _ _ _ _)
      (Ideal.absNorm v.asIdeal) (two_le_absNorm v)
  choose σv hσv using hσv
  set σ₁ : ℝ := max σ₀ 0 + ∑ v ∈ S' \ S, max (σv v) 0 with hσ₁
  have hσ₁₀ : σ₀ ≤ σ₁ := by
    have : 0 ≤ ∑ v ∈ S' \ S, max (σv v) 0 := Finset.sum_nonneg fun v _ => le_max_right _ _
    rw [hσ₁]; linarith [le_max_left σ₀ 0]
  have hσ₁v : ∀ v ∈ S' \ S, σv v ≤ σ₁ := by
    intro v hv
    have h1 : max (σv v) 0 ≤ ∑ w ∈ S' \ S, max (σv w) 0 :=
      Finset.single_le_sum (f := fun w => max (σv w) 0) (fun w _ => le_max_right _ _) hv
    rw [hσ₁]; linarith [le_max_left (σv v) 0, le_max_right σ₀ 0]

  set Q : ℂ → ℂ := fun s => ∏ v ∈ S' \ S, locEval Θ v s with hQ
  have hQdiff : Differentiable ℂ Q := by
    rw [hQ]; exact Differentiable.fun_finsetProd fun v _ => differentiable_locEval Θ v
  have hQ1 : Q 1 ≠ 0 := by
    rw [hQ]
    refine Finset.prod_ne_zero_iff.mpr fun v hv => ?_
    have hv' : v ∉ S := (Finset.mem_sdiff.mp hv).2
    have := hgen v hv'
    simpa only [locEval, locPoly, Complex.cpow_neg_one] using this
  refine ⟨σ₁, fun s => Λ s * Q s, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨a, ha, fun x hx => ?_⟩
    exact (hmero x hx).mul (hQdiff.analyticAt x).meromorphicAt
  ·
    have h1U : (1 : ℂ) ∈ {s : ℂ | a < s.re} := by
      simp only [Set.mem_setOf_eq, Complex.one_re]; exact ha
    have hQan : AnalyticAt ℂ Q 1 := hQdiff.analyticAt 1
    have hordQ : meromorphicOrderAt Q 1 = 0 := by
      rw [hQan.meromorphicOrderAt_eq, (hQan.analyticOrderAt_eq_zero).mpr hQ1]; rfl
    show meromorphicOrderAt (Λ * Q) 1 = -1
    rw [meromorphicOrderAt_mul (hmero 1 h1U) hQan.meromorphicAt, hordQ, add_zero]
    exact hord
  ·
    intro σ hσ
    show AnalyticAt ℂ (fun s => Λ s * Q s) (σ : ℂ)
    exact (han σ hσ).mul (hQdiff.analyticAt _)
  ·
    intro s hs
    have hs₀ : σ₀ < s.re := lt_of_le_of_lt hσ₁₀ hs
    have hne : ∀ v ∈ S' \ S, (locEval Θ v s)⁻¹ ≠ 0 := fun v hv =>
      inv_ne_zero (hσv v s (lt_of_le_of_lt (hσ₁v v hv) hs))
    have key := hasProd_subtype_notMem_of_subset (fun v => (locEval Θ v s)⁻¹) hSS' (hprod' s hs₀) hne
    simp only [inv_inv] at key
    exact key

end RS40M

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S →
      ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      meromorphicOrderAt Λ 1 = -1 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) :=
  RS40M.pole_of_pole0 K c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ

end
end S_AutomorphicForm_exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self (solution)
