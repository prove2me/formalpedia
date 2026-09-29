-- Prove2me | solution 1 for AutomorphicForm.exists_norm_eulerProduct_mul_intertwining_le_mul_of_abs_im_le_of_isInducedSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/deada12a-fad4-5d1d-a0aa-d799b9c14b8c

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.Analysis.Meromorphic.NormalForm
import Theorems.Thm_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation
import Theorems.Thm_AutomorphicForm_exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.ReImTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_eulerProduct_mul_intertwining_le_mul_of_abs_im_le_of_isInducedSection
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace"
p2m_attr_erase "instance" "NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply"
p2m_attr_erase "simp" "IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero"
p2m_attr_erase "simp" "LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply"
p2m_attr_erase "simp" "ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

section Interfaces

open Filter Topology

private theorem tprod_eq_inv_tprod_inv {ι : Type*} {f : ι → ℂ} (hm : Multipliable fun i => (f i)⁻¹)
    (h0 : (∏' i, (f i)⁻¹) ≠ 0) : ∏' i, f i = (∏' i, (f i)⁻¹)⁻¹ := by
  have ht : Tendsto (fun s : Finset ι => ∏ i ∈ s, (f i)⁻¹) (SummationFilter.unconditional ι).filter
      (𝓝 (∏' i, (f i)⁻¹)) := hm.hasProd
  have h : HasProd f (∏' i, (f i)⁻¹)⁻¹ := by
    refine (ht.inv₀ h0).congr fun s => ?_
    rw [Finset.prod_inv_distrib, inv_inv]
  exact h.tprod_eq

private theorem exists_pos_forall_le_iSup_norm {Y : Type*} [TopologicalSpace Y] {K : Set Y} (hK : IsCompact K)
    {Ψ : ℂ → Y → ℂ} (hc : Continuous fun p : ℂ × Y => Ψ p.1 p.2) {B : Set ℂ} (hB : IsCompact B)
    (hpos : ∀ s ∈ B, ∃ y ∈ K, Ψ s y ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ B, c ≤ ⨆ y : K, ‖Ψ s (y : Y)‖ := by
  have hgi : ∀ s, sSup ((fun y => ‖Ψ s y‖) '' K) = ⨆ y : K, ‖Ψ s (y : Y)‖ := fun s => sSup_image'
  have hcont : Continuous fun s => sSup ((fun y => ‖Ψ s y‖) '' K) :=
    hK.continuous_sSup (f := fun s y => ‖Ψ s y‖) (continuous_norm.comp hc)
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · exact ⟨1, one_pos, fun s hs => by simp [hBe] at hs⟩
  obtain ⟨s₀, hs₀, hmin⟩ := hB.exists_isMinOn hBne hcont.continuousOn
  obtain ⟨y₀, hy₀, hne⟩ := hpos s₀ hs₀
  have hcs₀ : Continuous fun y => Ψ s₀ y := hc.comp (continuous_const.prodMk continuous_id)
  have hbdd : BddAbove ((fun y => ‖Ψ s₀ y‖) '' K) :=
    hK.bddAbove_image (continuous_norm.comp hcs₀).continuousOn
  have hpos₀ : 0 < sSup ((fun y => ‖Ψ s₀ y‖) '' K) :=
    lt_of_lt_of_le (norm_pos_iff.mpr hne) (le_csSup hbdd ⟨y₀, hy₀, rfl⟩)
  refine ⟨sSup ((fun y => ‖Ψ s₀ y‖) '' K), hpos₀, fun s hs => ?_⟩
  rw [← hgi s]
  exact (isMinOn_iff.mp hmin) s hs

namespace MeromorphicNFAt p2m_export "MeromorphicNFAt" "eventuallyEq_nhdsNE_iff_eventuallyEq_nhds inv meromorphicAt" end MeromorphicNFAt
p2m_open_scoped "MeromorphicNFAt" in

private theorem MeromorphicNFAt.apply_eq_zero_of_not_analyticAt {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicNFAt f x)
    (h : ¬ AnalyticAt ℂ f x) : f x = 0 := by
  rcases meromorphicNFAt_iff_analyticAt_or.mp hf with ha | ⟨-, -, h0⟩
  · exact absurd ha h
  · exact h0

p2m_open_scoped "MeromorphicNFAt" in

private theorem MeromorphicNFAt.apply_eq_of_eventuallyEq_nhdsNE {f g : ℂ → ℂ} {x : ℂ} (hf : MeromorphicNFAt f x)
    (hg : MeromorphicNFAt g x) (h : f =ᶠ[𝓝[≠] x] g) : f x = g x :=
  ((hf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hg).mp h).eq_of_nhds

namespace MeromorphicOn p2m_export "MeromorphicOn" "sub neg inv congr add meromorphicOrderAt_ne_top_of_isPreconnected mul prod divisor toMeromorphicNFOn_eq_self_on_nhdsNE div" end MeromorphicOn
p2m_open_scoped "MeromorphicOn" in

private theorem MeromorphicOn.apply_eq_of_eqOn_of_analyticAt {Ω V : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {f h : ℂ → ℂ} (hf : MeromorphicOn f Ω) (hh : AnalyticOnNhd ℂ h Ω) (hV : IsOpen V) (hVne : V.Nonempty)
    (hVΩ : V ⊆ Ω) (heq : Set.EqOn f h V) {x : ℂ} (hx : x ∈ Ω) (hfx : AnalyticAt ℂ f x) : f x = h x := by
  have _ := hΩ
  obtain ⟨v, hv⟩ := hVne
  have hg : MeromorphicOn (f - h) Ω := hf.sub hh.meromorphicOn
  have htop_v : meromorphicOrderAt (f - h) v = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hz : ∀ᶠ z in 𝓝 v, (f - h) z = 0 := by
      filter_upwards [hV.mem_nhds hv] with z hz
      simp [heq hz]
    exact hz.filter_mono nhdsWithin_le_nhds
  have htop_x : meromorphicOrderAt (f - h) x = ⊤ := by
    by_contra hne
    exact hg.meromorphicOrderAt_ne_top_of_isPreconnected hΩc hx (hVΩ hv) hne htop_v
  have hev : ∀ᶠ z in 𝓝[≠] x, (f - h) z = 0 := meromorphicOrderAt_eq_top_iff.mp htop_x
  have h1 : Tendsto (f - h) (𝓝[≠] x) (𝓝 ((f - h) x)) :=
    ((hfx.sub (hh x hx)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (f - h) (𝓝[≠] x) (𝓝 0) :=
    tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm)
  have h3 : (f - h) x = 0 := tendsto_nhds_unique h1 h2
  simpa [sub_eq_zero] using h3

section EntireFamilyDivisionEngine

open Filter Topology Metric Set

namespace EntireFamilyDivision

variable {Y : Type*}

private noncomputable def step (Φ : ℂ → Y → ℂ) (a : ℂ) : ℂ → Y → ℂ :=
  fun s y => dslope (fun t => Φ t y) a s

private theorem step_apply (Φ : ℂ → Y → ℂ) (a s : ℂ) (y : Y) :
    step Φ a s y = dslope (fun t => Φ t y) a s := rfl

private theorem differentiable_step {Φ : ℂ → Y → ℂ} (hd : ∀ y, Differentiable ℂ fun s => Φ s y) (a : ℂ) (y : Y) :
    Differentiable ℂ fun s => step Φ a s y := by
  have h := (Complex.differentiableOn_dslope (f := fun t => Φ t y) (c := a) univ_mem).2 (hd y).differentiableOn
  exact differentiableOn_univ.1 h

private theorem dslope_sub_apply {f g : ℂ → ℂ} {a : ℂ} (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g a)
    (s : ℂ) : dslope (fun t => f t - g t) a s = dslope f a s - dslope g a s := by
  by_cases h : s = a
  · subst h
    simp only [dslope_same]
    exact deriv_sub hf hg
  · simp only [dslope_of_ne _ h, slope_def_field]
    ring

private theorem step_sub_step {Φ : ℂ → Y → ℂ} (hd : ∀ y, Differentiable ℂ fun s => Φ s y) (a s : ℂ) (y y' : Y) :
    dslope (fun t => Φ t y - Φ t y') a s = step Φ a s y - step Φ a s y' :=
  dslope_sub_apply ((hd y).differentiableAt) ((hd y').differentiableAt) s

private theorem continuous_step [TopologicalSpace Y] {Φ : ℂ → Y → ℂ} (hc : Continuous fun p : ℂ × Y => Φ p.1 p.2)
    (hd : ∀ y, Differentiable ℂ fun s => Φ s y) (a : ℂ) :
    Continuous fun p : ℂ × Y => step Φ a p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, y₀⟩
  by_cases hs : s₀ = a
  · subst hs
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have h1 : ∀ᶠ s in 𝓝 s₀, dist (step Φ s₀ s y₀) (step Φ s₀ s₀ y₀) < ε / 2 :=
      Metric.tendsto_nhds.1 (differentiable_step hd s₀ y₀).continuous.continuousAt _ (by positivity)
    have h3 : ∀ᶠ s in 𝓝 s₀, s ∈ ball s₀ 1 := ball_mem_nhds s₀ one_pos
    have h2 : ∀ᶠ y in 𝓝 y₀, ∀ w ∈ closedBall s₀ 1, ‖Φ w y - Φ w y₀‖ ≤ ε / 8 := by
      refine (isCompact_closedBall s₀ 1).eventually_forall_of_forall_eventually fun w _ => ?_
      have hF : Continuous fun z : Y × ℂ => ‖Φ z.2 z.1 - Φ z.2 y₀‖ :=
        ((hc.comp (continuous_snd.prodMk continuous_fst)).sub
          (hc.comp (continuous_snd.prodMk continuous_const))).norm
      have hlim : Tendsto (fun z : Y × ℂ => ‖Φ z.2 z.1 - Φ z.2 y₀‖) (𝓝 (y₀, w)) (𝓝 0) := by
        simpa [ContinuousAt] using hF.continuousAt (x := (y₀, w))
      exact (hlim.eventually_lt_const (by positivity : (0 : ℝ) < ε / 8)).mono fun z hz => hz.le
    rw [nhds_prod_eq]
    filter_upwards [(h1.and h3).prod_mk h2] with p hp
    obtain ⟨⟨hp1, hp3⟩, hp2⟩ := hp
    have hD : ‖dslope (fun t => Φ t p.2 - Φ t y₀) s₀ p.1‖ ≤ ε / 4 / 1 := by
      refine Complex.norm_dslope_le_div_of_mapsTo_ball (c := s₀) (R₁ := 1) (R₂ := ε / 4) ?_ ?_ hp3
      · exact ((hd p.2).sub (hd y₀)).differentiableOn
      · intro w hw
        rw [mem_closedBall, dist_eq_norm]
        calc ‖Φ w p.2 - Φ w y₀ - (Φ s₀ p.2 - Φ s₀ y₀)‖
            ≤ ‖Φ w p.2 - Φ w y₀‖ + ‖Φ s₀ p.2 - Φ s₀ y₀‖ := norm_sub_le _ _
          _ ≤ ε / 8 + ε / 8 :=
            add_le_add (hp2 w (ball_subset_closedBall hw)) (hp2 s₀ (mem_closedBall_self zero_le_one))
          _ = ε / 4 := by ring
    rw [step_sub_step hd, div_one] at hD
    rw [dist_eq_norm] at hp1 ⊢
    calc ‖step Φ s₀ p.1 p.2 - step Φ s₀ s₀ y₀‖
        = ‖(step Φ s₀ p.1 p.2 - step Φ s₀ p.1 y₀) + (step Φ s₀ p.1 y₀ - step Φ s₀ s₀ y₀)‖ := by ring_nf
      _ ≤ ‖step Φ s₀ p.1 p.2 - step Φ s₀ p.1 y₀‖ + ‖step Φ s₀ p.1 y₀ - step Φ s₀ s₀ y₀‖ := norm_add_le _ _
      _ < ε := by linarith
  · have hev : ∀ᶠ p : ℂ × Y in 𝓝 (s₀, y₀), (Φ p.1 p.2 - Φ a p.2) / (p.1 - a) = step Φ a p.1 p.2 := by
      have hne : ∀ᶠ p : ℂ × Y in 𝓝 (s₀, y₀), p.1 ≠ a := continuous_fst.continuousAt.eventually_ne hs
      filter_upwards [hne] with p hp
      simp only [step_apply, dslope_of_ne _ hp, slope_def_field]
    refine ContinuousAt.congr ?_ hev
    refine ContinuousAt.div₀ ?_ ?_ (sub_ne_zero.2 hs)
    · exact (hc.sub (hc.comp (continuous_const.prodMk continuous_snd))).continuousAt
    · exact (continuous_fst.sub continuous_const).continuousAt

private noncomputable def iter (Φ : ℂ → Y → ℂ) (a : ℂ) : ℕ → ℂ → Y → ℂ
  | 0 => Φ
  | n + 1 => step (iter Φ a n) a

private theorem iter_zero (Φ : ℂ → Y → ℂ) (a : ℂ) : iter Φ a 0 = Φ := rfl

private theorem iter_succ (Φ : ℂ → Y → ℂ) (a : ℂ) (n : ℕ) : iter Φ a (n + 1) = step (iter Φ a n) a := rfl

private theorem iter_succ_eq_iter_step (Φ : ℂ → Y → ℂ) (a : ℂ) : ∀ n : ℕ, iter Φ a (n + 1) = iter (step Φ a) a n
  | 0 => rfl
  | n + 1 => by rw [iter_succ, iter_succ_eq_iter_step Φ a n, ← iter_succ]

private theorem differentiable_iter {Φ : ℂ → Y → ℂ} (hd : ∀ y, Differentiable ℂ fun s => Φ s y) (a : ℂ) :
    ∀ n : ℕ, ∀ y, Differentiable ℂ fun s => iter Φ a n s y
  | 0 => hd
  | n + 1 => fun y => differentiable_step (differentiable_iter hd a n) a y

private theorem continuous_iter [TopologicalSpace Y] {Φ : ℂ → Y → ℂ} (hc : Continuous fun p : ℂ × Y => Φ p.1 p.2)
    (hd : ∀ y, Differentiable ℂ fun s => Φ s y) (a : ℂ) :
    ∀ n : ℕ, Continuous fun p : ℂ × Y => iter Φ a n p.1 p.2
  | 0 => hc
  | n + 1 => continuous_step (continuous_iter hc hd a n) (differentiable_iter hd a n) a

private theorem eq_pow_mul_iter (Φ : ℂ → Y → ℂ) (a : ℂ) (y : Y) :
    ∀ n : ℕ, (∀ k < n, iter Φ a k a y = 0) → ∀ s, Φ s y = (s - a) ^ n * iter Φ a n s y
  | 0, _, s => by simp [iter_zero]
  | n + 1, h, s => by
    have h1 : Φ s y = (s - a) ^ n * iter Φ a n s y :=
      eq_pow_mul_iter Φ a y n (fun k hk => h k (Nat.lt_succ_of_lt hk)) s
    have h2 : (s - a) * iter Φ a (n + 1) s y = iter Φ a n s y := by
      have := sub_smul_dslope_of_zero (f := fun t => iter Φ a n t y) (a := a) (h n n.lt_succ_self) s
      simpa [iter_succ, step_apply] using this
    rw [h1, ← h2, pow_succ]
    ring

private theorem analyticOrderAt_eq_dslope_add_one {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℂ} (h0 : f a = 0) :
    analyticOrderAt f a = analyticOrderAt (dslope f a) a + 1 := by
  have hfe : (dslope f a) * (fun z => z - a) = f := by
    funext z
    have := sub_smul_dslope_of_zero h0 z
    rw [smul_eq_mul] at this
    simp only [Pi.mul_apply]
    rw [mul_comm]
    exact this
  have hds : Differentiable ℂ (dslope f a) :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope (c := a) univ_mem).2 hf.differentiableOn)
  have hlin : analyticOrderAt (fun z : ℂ => z - a) a = 1 := by
    refine (analyticAt_id.sub analyticAt_const).analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp) ?_
    simp
  calc analyticOrderAt f a = analyticOrderAt ((dslope f a) * (fun z => z - a)) a := by rw [hfe]
    _ = analyticOrderAt (dslope f a) a + analyticOrderAt (fun z : ℂ => z - a) a :=
        analyticOrderAt_mul (hds.analyticAt a) (analyticAt_id.sub analyticAt_const)
    _ = analyticOrderAt (dslope f a) a + 1 := by rw [hlin]

private theorem analyticOrderAt_step_add_one {Φ : ℂ → Y → ℂ} (hd : ∀ y, Differentiable ℂ fun s => Φ s y) {a : ℂ}
    {y : Y} (h0 : Φ a y = 0) :
    analyticOrderAt (fun s => Φ s y) a = analyticOrderAt (fun s => step Φ a s y) a + 1 :=
  analyticOrderAt_eq_dslope_add_one (hd y) h0

private theorem iter_apply_eq_zero_of_lt_analyticOrderAt :
    ∀ (k : ℕ) {Φ : ℂ → Y → ℂ}, (∀ y, Differentiable ℂ fun s => Φ s y) → ∀ {a : ℂ} {y : Y},
      (k : ℕ∞) < analyticOrderAt (fun s => Φ s y) a → iter Φ a k a y = 0
  | 0, Φ, _, a, y, hk => by
    rw [iter_zero]
    exact apply_eq_zero_of_analyticOrderAt_ne_zero (f := fun s => Φ s y) (by simpa using hk.ne')
  | k + 1, Φ, hd, a, y, hk => by
    have h0 : Φ a y = 0 := by
      refine apply_eq_zero_of_analyticOrderAt_ne_zero (f := fun s => Φ s y) ?_
      exact ne_of_gt (lt_of_le_of_lt (by simp) hk)
    rw [analyticOrderAt_step_add_one hd h0] at hk
    have hk' : (k : ℕ∞) < analyticOrderAt (fun s => step Φ a s y) a := by
      have hk2 : (k : ℕ∞) + 1 < analyticOrderAt (fun s => step Φ a s y) a + 1 := by
        simpa [Nat.cast_succ] using hk
      exact (WithTop.add_lt_add_iff_right ENat.one_ne_top).1 hk2
    rw [iter_succ_eq_iter_step]
    exact iter_apply_eq_zero_of_lt_analyticOrderAt k (differentiable_step hd a) hk'

private theorem analyticOrderAt_iter_add :
    ∀ (n : ℕ) {Φ : ℂ → Y → ℂ}, (∀ y, Differentiable ℂ fun s => Φ s y) → ∀ {a : ℂ} {y : Y},
      (n : ℕ∞) ≤ analyticOrderAt (fun s => Φ s y) a →
      analyticOrderAt (fun s => iter Φ a n s y) a + n = analyticOrderAt (fun s => Φ s y) a
  | 0, Φ, _, a, y, _ => by simp [iter_zero]
  | n + 1, Φ, hd, a, y, hn => by
    have h0 : Φ a y = 0 := by
      refine apply_eq_zero_of_analyticOrderAt_ne_zero (f := fun s => Φ s y) ?_
      exact ne_of_gt (lt_of_lt_of_le (by simp) hn)
    have hrec := analyticOrderAt_step_add_one hd h0
    have hn' : (n : ℕ∞) ≤ analyticOrderAt (fun s => step Φ a s y) a := by
      have hn2 : (n : ℕ∞) + 1 ≤ analyticOrderAt (fun s => step Φ a s y) a + 1 := by
        rw [hrec] at hn
        simpa [Nat.cast_succ] using hn
      exact (WithTop.add_le_add_iff_right ENat.one_ne_top).1 hn2
    have ih := analyticOrderAt_iter_add n (differentiable_step hd a) hn'
    rw [iter_succ_eq_iter_step]
    rw [hrec, ← ih, Nat.cast_succ, add_assoc]

private theorem analyticOrderAt_ne_top_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f ≠ 0) (a : ℂ) :
    analyticOrderAt f a ≠ ⊤ := by
  rw [Ne, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero a (fun z => hf.analyticAt z)]
  exact hf0

private theorem exists_pow_mul_of_ne_zero [TopologicalSpace Y] {Φ : ℂ → Y → ℂ}
    (hc : Continuous fun p : ℂ × Y => Φ p.1 p.2)
    (hd : ∀ y, Differentiable ℂ fun s => Φ s y) (a : ℂ) (hne : ∃ y, (fun s => Φ s y) ≠ 0) :
    ∃ (m : ℕ) (Ψ : ℂ → Y → ℂ), (Continuous fun p : ℂ × Y => Ψ p.1 p.2) ∧
      (∀ y, Differentiable ℂ fun s => Ψ s y) ∧ (∀ s y, Φ s y = (s - a) ^ m * Ψ s y) ∧ ∃ y, Ψ a y ≠ 0 := by
  classical
  obtain ⟨y₁, hy₁⟩ := hne
  have hfin : ∃ n : ℕ, ∃ y, analyticOrderAt (fun s => Φ s y) a = n := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_ne_top_of_ne_zero (hd y₁) hy₁ a)
    exact ⟨n, y₁, hn.symm⟩
  set m := Nat.find hfin with hm
  obtain ⟨y₂, hy₂⟩ := Nat.find_spec hfin
  have hge : ∀ y, (m : ℕ∞) ≤ analyticOrderAt (fun s => Φ s y) a := by
    intro y
    rcases eq_or_ne (analyticOrderAt (fun s => Φ s y) a) ⊤ with h | h
    · rw [h]; exact le_top
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
      rw [← hn]
      exact_mod_cast Nat.find_min' hfin ⟨y, hn.symm⟩
  refine ⟨m, iter Φ a m, continuous_iter hc hd a m, differentiable_iter hd a m, ?_, y₂, ?_⟩
  · intro s y
    refine eq_pow_mul_iter Φ a y m (fun k hk => ?_) s
    refine iter_apply_eq_zero_of_lt_analyticOrderAt k hd (lt_of_lt_of_le ?_ (hge y))
    exact_mod_cast hk
  · have h := analyticOrderAt_iter_add m hd (a := a) (y := y₂) (hy₂ ▸ le_rfl)
    rw [hy₂] at h
    have h0 : analyticOrderAt (fun s => iter Φ a m s y₂) a = 0 := by
      have h' : analyticOrderAt (fun s => iter Φ a m s y₂) a + (m : ℕ∞) = 0 + (m : ℕ∞) := by
        rw [h, zero_add]
      exact WithTop.add_right_cancel (ENat.coe_ne_top m) h'
    rcases analyticOrderAt_eq_zero.1 h0 with hna | hv
    · exact absurd ((differentiable_iter hd a m y₂).analyticAt a) hna
    · exact hv

private theorem exists_prod_mul_of_finset [TopologicalSpace Y] (B : Set ℂ) (S : Finset ℂ) :
    ∀ (Φ : ℂ → Y → ℂ), (Continuous fun p : ℂ × Y => Φ p.1 p.2) → (∀ y, Differentiable ℂ fun s => Φ s y) →
      (∃ y, (fun s => Φ s y) ≠ 0) → (∀ s ∈ B, s ∉ S → ∃ y, Φ s y ≠ 0) →
      ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (Ψ : ℂ → Y → ℂ), Z ⊆ S ∧ (Continuous fun p : ℂ × Y => Ψ p.1 p.2) ∧
        (∀ y, Differentiable ℂ fun s => Ψ s y) ∧
        (∀ s y, Φ s y = (∏ z ∈ Z, (s - z) ^ m z) * Ψ s y) ∧ (∀ s ∈ B, ∃ y, Ψ s y ≠ 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro Φ hc hd _ hinv
    exact ⟨∅, fun _ => 0, Φ, Finset.Subset.refl ∅, hc, hd, fun s y => by simp,
      fun s hs => hinv s hs (Finset.notMem_empty s)⟩
  | insert a S ha ih =>
    intro Φ hc hd hne hinv
    obtain ⟨m₀, Ψ₁, hc₁, hd₁, hfac₁, y₀, hy₀⟩ := exists_pow_mul_of_ne_zero hc hd a hne
    have hne₁ : ∃ y, (fun s => Ψ₁ s y) ≠ 0 := by
      obtain ⟨y, hy⟩ := hne
      refine ⟨y, fun h => hy ?_⟩
      funext s
      have hs := congrFun h s
      simp only [Pi.zero_apply] at hs
      simp [hfac₁ s y, hs]
    have hinv₁ : ∀ s ∈ B, s ∉ S → ∃ y, Ψ₁ s y ≠ 0 := by
      intro s hs hsS
      by_cases hsa : s = a
      · subst hsa
        exact ⟨y₀, hy₀⟩
      · obtain ⟨y, hy⟩ := hinv s hs (by simp [hsa, hsS])
        refine ⟨y, fun h => hy ?_⟩
        rw [hfac₁ s y, h, mul_zero]
    obtain ⟨Z, m, Ψ, hZS, hcΨ, hdΨ, hfac, hB⟩ := ih Ψ₁ hc₁ hd₁ hne₁ hinv₁
    have haZ : a ∉ Z := fun h => ha (hZS h)
    refine ⟨insert a Z, fun z => if z = a then m₀ else m z, Ψ, Finset.insert_subset_insert a hZS, hcΨ, hdΨ,
      ?_, hB⟩
    intro s y
    have hprod : (∏ z ∈ insert a Z, (s - z) ^ (if z = a then m₀ else m z)) =
        (s - a) ^ m₀ * ∏ z ∈ Z, (s - z) ^ m z := by
      rw [Finset.prod_insert haZ, if_pos (rfl : a = a)]
      congr 1
      refine Finset.prod_congr rfl fun z hz => ?_
      have hza : z ≠ a := fun h => haZ (h ▸ hz)
      rw [if_neg hza]
    rw [hprod, hfac₁ s y, hfac s y]
    ring

end EntireFamilyDivision

namespace EntireFamilyDivision

private theorem finite_inter_zero_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f ≠ 0) {B : Set ℂ}
    (hB : IsCompact B) : (B ∩ {s | f s = 0}).Finite := by
  have hiso : ∀ z : ℂ, ∀ᶠ t in 𝓝[≠] z, f t ≠ 0 := by
    intro z
    by_contra h
    rw [Filter.not_eventually] at h
    have hfw : ∃ᶠ t in 𝓝[≠] z, f t = 0 := h.mono fun t ht => not_not.mp ht
    have hU : AnalyticOnNhd ℂ f univ := fun w _ => hf.analyticAt w
    have hzero : EqOn f 0 univ :=
      hU.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ z) hfw
    exact hf0 (funext fun w => hzero (mem_univ w))
  refine IsCompact.finite (hB.inter_right (isClosed_eq hf.continuous continuous_const)) ?_
  rw [isDiscrete_iff_nhdsNE]
  intro x _
  rw [inf_principal_eq_bot]
  exact Filter.mem_of_superset (hiso x) fun t ht hmem => ht hmem.2

private theorem differentiable_prod_pow (Z : Finset ℂ) (m : ℂ → ℕ) :
    Differentiable ℂ fun s : ℂ => ∏ z ∈ Z, (s - z) ^ m z :=
  Differentiable.fun_finsetProd fun z _ => by fun_prop

private theorem eventually_prod_pow_ne_zero (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) :
    ∀ᶠ t in 𝓝[≠] s, ∏ z ∈ Z, (t - z) ^ m z ≠ 0 := by
  have h : ∀ᶠ t in 𝓝[≠] s, ∀ z ∈ Z, t ≠ z := by
    rw [Filter.eventually_all_finset]
    intro z _
    rcases eq_or_ne z s with rfl | hzs
    · exact eventually_mem_nhdsWithin.mono fun t ht => by simpa using ht
    · exact eventually_ne_nhdsWithin hzs.symm
  exact h.mono fun t ht => Finset.prod_ne_zero_iff.2 fun z hz => pow_ne_zero _ (sub_ne_zero.2 (ht z hz))

end EntireFamilyDivision

private theorem EntireFamilyDivision.exists_divisor_family {Y : Type*} [TopologicalSpace Y] {Φ : ℂ → Y → ℂ}
    (hc : Continuous fun p : ℂ × Y => Φ p.1 p.2) (hd : ∀ y, Differentiable ℂ fun s => Φ s y)
    {B : Set ℂ} (hB : IsCompact B) (hne : ∃ s y, Φ s y ≠ 0) :
    ∃ (P : ℂ → ℂ) (Ψ : ℂ → Y → ℂ), Differentiable ℂ P ∧ (∀ s : ℂ, ∀ᶠ t in 𝓝[≠] s, P t ≠ 0) ∧
      (Continuous fun p : ℂ × Y => Ψ p.1 p.2) ∧ (∀ y, Differentiable ℂ fun s => Ψ s y) ∧
      (∀ s y, Φ s y = P s * Ψ s y) ∧ (∀ s ∈ B, ∃ y, Ψ s y ≠ 0) := by
  classical
  obtain ⟨s₁, y₁, hs₁⟩ := hne
  have hf0 : (fun s => Φ s y₁) ≠ 0 := fun h => hs₁ (by simpa using congrFun h s₁)
  have hfin := EntireFamilyDivision.finite_inter_zero_of_ne_zero (hd y₁) hf0 hB
  obtain ⟨Z, m, Ψ, -, hcΨ, hdΨ, hfac, hBΨ⟩ :=
    EntireFamilyDivision.exists_prod_mul_of_finset B hfin.toFinset Φ hc hd ⟨y₁, hf0⟩
      fun s hs hsS => ⟨y₁, fun h0 => hsS (hfin.mem_toFinset.2 ⟨hs, h0⟩)⟩
  exact ⟨fun s => ∏ z ∈ Z, (s - z) ^ m z, Ψ, EntireFamilyDivision.differentiable_prod_pow Z m,
    EntireFamilyDivision.eventually_prod_pow_ne_zero Z m, hcΨ, hdΨ, hfac, hBΨ⟩

end EntireFamilyDivisionEngine

end Interfaces

namespace QuotientSectionFamily

open Filter Topology

private theorem eq_of_eventuallyEq_nhdsNE {f g : ℂ → ℂ} {s₀ : ℂ} (hf : ContinuousAt f s₀)
    (hg : ContinuousAt g s₀) (h : ∀ᶠ s in 𝓝[≠] s₀, f s = g s) : f s₀ = g s₀ := by
  have h1 : Tendsto f (𝓝[≠] s₀) (𝓝 (f s₀)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto g (𝓝[≠] s₀) (𝓝 (g s₀)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique (h1.congr' h) h2

private theorem mem_of_eventually_mem_nhdsNE {ι : Type*} (W : Submodule ℂ (ι → ℂ)) [FiniteDimensional ℂ W]
    (Fn : ℂ → ι → ℂ) (hcont : ∀ i, Continuous fun s => Fn s i) (s₀ : ℂ)
    (h : ∀ᶠ s in 𝓝[≠] s₀, Fn s ∈ W) : Fn s₀ ∈ W := by
  have hFn : Continuous Fn := continuous_pi hcont
  exact W.closed_of_finiteDimensional.mem_of_tendsto
    (hFn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h

private theorem rightTranslatesSpanFinite_of_forall_mem {G : Type*} [Group G] (K : Subgroup G) (f : G → ℂ)
    (W : Submodule ℂ (↥K → ℂ)) [FiniteDimensional ℂ W]
    (h : ∀ g : G, (fun k : ↥K => f (g * (k : G))) ∈ W) : RightTranslatesSpanFinite K f := by
  classical
  let Λ : Module.Dual ℂ ↥W →ₗ[ℂ] (G → ℂ) :=
    LinearMap.pi fun g : G => LinearMap.applyₗ (⟨fun k : ↥K => f (g * (k : G)), h g⟩ : ↥W)
  have hfin : (LinearMap.range Λ).FG := (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  obtain ⟨S, hS⟩ := hfin
  refine ⟨S, fun k hk => ?_⟩
  rw [hS, LinearMap.mem_range]
  refine ⟨(LinearMap.proj (⟨k, hk⟩ : ↥K)).comp W.subtype, ?_⟩
  funext g
  simp [Λ]

section Eta

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_etaFst_val (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (x : (AdeleRing (𝓞 F) F)ˣ) :
    Continuous fun s : ℂ => ((etaFst μ α hα s x : ℂˣ) : ℂ) := by
  have hb : ((((α x : ℝˣ) : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hα x).ne'
  have h1 : Continuous fun s : ℂ => ((((α x : ℝˣ) : ℝ)) : ℂ) ^ (s + 1 / 2) :=
    (continuous_iff_continuousAt.2 fun _ => continuousAt_const_cpow hb).comp
      (continuous_id.add continuous_const)
  have h2 : (fun s : ℂ => ((etaFst μ α hα s x : ℂˣ) : ℂ)) =
      fun s => ((μ x : ℂˣ) : ℂ) * ((((α x : ℝˣ) : ℝ)) : ℂ) ^ (s + 1 / 2) := by
    funext s
    rw [etaFst_apply, Units.val_mul, cpowChar_apply_val]
  rw [h2]
  exact continuous_const.mul h1

private theorem continuous_etaSnd_val (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (x : (AdeleRing (𝓞 F) F)ˣ) :
    Continuous fun s : ℂ => ((etaSnd ν α hα s x : ℂˣ) : ℂ) := by
  have hb : ((((α x : ℝˣ) : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hα x).ne'
  have h1 : Continuous fun s : ℂ => ((((α x : ℝˣ) : ℝ)) : ℂ) ^ (-(s + 1 / 2)) :=
    (continuous_iff_continuousAt.2 fun _ => continuousAt_const_cpow hb).comp
      (continuous_id.add continuous_const).neg
  have h2 : (fun s : ℂ => ((etaSnd ν α hα s x : ℂˣ) : ℂ)) =
      fun s => ((ν x : ℂˣ) : ℂ) * ((((α x : ℝˣ) : ℝ)) : ℂ) ^ (-(s + 1 / 2)) := by
    funext s
    rw [etaSnd_apply, Units.val_mul, cpowChar_apply_val]
  rw [h2]
  exact continuous_const.mul h1

end Eta

private theorem exists_isOpen_subgroup_forall_apply_mul_eq_of_isKfSmooth_of_continuous_of_differentiable
    (F : Type) [Field F] [NumberField F] (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφf : ∀ s : ℂ, IsKfSmooth F (φ s))
    (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    (hφhol : ∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => φ s g)) :
    ∃ K' : Subgroup ↥(finiteAdelicGL2Subgroup F), IsOpen (K' : Set ↥(finiteAdelicGL2Subgroup F)) ∧
      ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), ∀ k ∈ K', φ s (g * (k : AdelicGL2 (𝓞 F) F)) = φ s g := by
  have _ := hφjc
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : SecondCountableTopology ↥(finiteAdelicGL2Subgroup F) :=
    inferInstanceAs (SecondCountableTopology ↥(finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F)))
  obtain ⟨B, hB⟩ := (nhds (1 : ↥(finiteAdelicGL2Subgroup F))).exists_antitone_basis
  have hZc : ∀ n : ℕ,
      IsClosed {s : ℂ | ∀ k ∈ B n, ∀ g : AdelicGL2 (𝓞 F) F, φ s (g * (k : AdelicGL2 (𝓞 F) F)) = φ s g} := by
    intro n
    have hZ : {s : ℂ | ∀ k ∈ B n, ∀ g : AdelicGL2 (𝓞 F) F, φ s (g * (k : AdelicGL2 (𝓞 F) F)) = φ s g} =
        ⋂ k ∈ B n, ⋂ g : AdelicGL2 (𝓞 F) F, {s : ℂ | φ s (g * (k : AdelicGL2 (𝓞 F) F)) = φ s g} := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hZ]
    exact isClosed_biInter fun k _ =>
      isClosed_iInter fun g => isClosed_eq (hφhol _).continuous (hφhol g).continuous
  have hcover : (⋃ n : ℕ,
      {s : ℂ | ∀ k ∈ B n, ∀ g : AdelicGL2 (𝓞 F) F, φ s (g * (k : AdelicGL2 (𝓞 F) F)) = φ s g}) = Set.univ := by
    refine Set.eq_univ_of_forall fun s => Set.mem_iUnion.2 ?_
    have hst : IsOpen ((MulAction.stabilizer ↥(finiteAdelicGL2Subgroup F)
        (FLT.SmoothVectors.RightTranslationFn.mk (φ s) : FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
          Subgroup ↥(finiteAdelicGL2Subgroup F)) : Set ↥(finiteAdelicGL2Subgroup F)) :=
      hφf s
    obtain ⟨n, -, hn⟩ := hB.toHasBasis.mem_iff.1 (hst.mem_nhds (Subgroup.one_mem _))
    exact ⟨n, fun k hk g =>
      congrFun (congrArg FLT.SmoothVectors.RightTranslationFn.toFun (MulAction.mem_stabilizer_iff.1 (hn hk))) g⟩
  obtain ⟨n, s₀, hs₀⟩ := nonempty_interior_of_iUnion_of_closed hZc hcover
  have hfix : ∀ k ∈ B n, ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s (g * (k : AdelicGL2 (𝓞 F) F)) = φ s g := by
    intro k hk s g
    have hd : AnalyticOnNhd ℂ (fun z : ℂ => φ z (g * (k : AdelicGL2 (𝓞 F) F)) - φ z g) Set.univ :=
      ((hφhol _).sub (hφhol g)).differentiableOn.analyticOnNhd isOpen_univ
    have hev : (fun z : ℂ => φ z (g * (k : AdelicGL2 (𝓞 F) F)) - φ z g) =ᶠ[nhds s₀] 0 := by
      filter_upwards [isOpen_interior.mem_nhds hs₀] with z hz
      exact sub_eq_zero.2 (interior_subset hz k hk g)
    exact sub_eq_zero.1
      (hd.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ s₀) hev (Set.mem_univ s))
  refine ⟨⨅ s : ℂ, MulAction.stabilizer ↥(finiteAdelicGL2Subgroup F)
        (FLT.SmoothVectors.RightTranslationFn.mk (φ s) :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ), ?_, ?_⟩
  · refine Subgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset (hB.toHasBasis.mem_of_mem (i := n) trivial) fun k hk => ?_)
    exact Subgroup.mem_iInf.2 fun s =>
      MulAction.mem_stabilizer_iff.2 (FLT.SmoothVectors.RightTranslationFn.ext fun g => hfix k hk s g)
  · intro s g k hk
    exact congrFun
      (congrArg FLT.SmoothVectors.RightTranslationFn.toFun
        (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_iInf.1 hk s))) g

section Transfer

variable {F : Type} [Field F] [NumberField F]
variable {P : ℂ → ℂ} {φ ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ}

private theorem psi_eq_inv_mul (hfac : ∀ s g, φ s g = P s * ψ s g) {s : ℂ} (hPs : P s ≠ 0)
    (g : AdelicGL2 (𝓞 F) F) : ψ s g = (P s)⁻¹ * φ s g := by
  rw [hfac s g, inv_mul_cancel_left₀ hPs]

private theorem isInducedSection_quotient (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
    (hP : ∀ s : ℂ, ∀ᶠ t in 𝓝[≠] s, P t ≠ 0) (hfac : ∀ s g, φ s g = P s * ψ s g)
    (hψhol : ∀ g, Differentiable ℂ fun s => ψ s g) (s₀ : ℂ) :
    IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) (ψ s₀) := by
  unfold IsInducedSection
  intro b hb g
  have hev : ∀ᶠ s in 𝓝[≠] s₀, ψ s (b * g) =
      ((etaFst μ α hα s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((etaSnd ν α hα s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * ψ s g := by
    filter_upwards [hP s₀] with s hs
    rw [psi_eq_inv_mul hfac hs, psi_eq_inv_mul hfac hs, hφ s b hb g]
    ring
  refine eq_of_eventuallyEq_nhdsNE (f := fun s => ψ s (b * g)) ?_ ?_ hev
  · exact (hψhol (b * g)).continuous.continuousAt
  · exact ((continuous_etaFst_val μ α hα _).mul (continuous_etaSnd_val ν α hα _)).mul
      (hψhol g).continuous |>.continuousAt

private theorem forall_apply_mul_eq_quotient (hP : ∀ s : ℂ, ∀ᶠ t in 𝓝[≠] s, P t ≠ 0)
    (hfac : ∀ s g, φ s g = P s * ψ s g) (hψhol : ∀ g, Differentiable ℂ fun s => ψ s g)
    (K' : Subgroup ↥(finiteAdelicGL2Subgroup F))
    (hK' : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), ∀ k ∈ K', φ s (g * (k : AdelicGL2 (𝓞 F) F)) = φ s g)
    (s₀ : ℂ) (g : AdelicGL2 (𝓞 F) F) {k : ↥(finiteAdelicGL2Subgroup F)} (hk : k ∈ K') :
    ψ s₀ (g * (k : AdelicGL2 (𝓞 F) F)) = ψ s₀ g := by
  have hev : ∀ᶠ s in 𝓝[≠] s₀, ψ s (g * (k : AdelicGL2 (𝓞 F) F)) = ψ s g := by
    filter_upwards [hP s₀] with s hs
    rw [psi_eq_inv_mul hfac hs, psi_eq_inv_mul hfac hs, hK' s g k hk]
  exact eq_of_eventuallyEq_nhdsNE (f := fun s => ψ s (g * (k : AdelicGL2 (𝓞 F) F))) (g := fun s => ψ s g)
    (hψhol _).continuous.continuousAt (hψhol g).continuous.continuousAt hev

private theorem isKfSmooth_of_subgroup {χ : AdelicGL2 (𝓞 F) F → ℂ} (K' : Subgroup ↥(finiteAdelicGL2Subgroup F))
    (hK'o : IsOpen (K' : Set ↥(finiteAdelicGL2Subgroup F)))
    (hfix : ∀ (g : AdelicGL2 (𝓞 F) F), ∀ k ∈ K', χ (g * (k : AdelicGL2 (𝓞 F) F)) = χ g) : IsKfSmooth F χ := by
  rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup]
  refine ⟨K', hK'o, fun u hu => ?_⟩
  exact FLT.SmoothVectors.RightTranslationFn.ext fun g => hfix g u hu

private theorem slice_mem_quotient (hP : ∀ s : ℂ, ∀ᶠ t in 𝓝[≠] s, P t ≠ 0)
    (hfac : ∀ s g, φ s g = P s * ψ s g) (hψhol : ∀ g, Differentiable ℂ fun s => ψ s g)
    (w : InfinitePlace F) (W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ)) (hW : FiniteDimensional ℂ W)
    (hφW : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
      (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
    (s₀ : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    (fun k : ↥(archRowIsometrySubgroup F w) => ψ s₀ (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W := by
  haveI := hW
  refine mem_of_eventually_mem_nhdsNE W
    (fun s => fun k : ↥(archRowIsometrySubgroup F w) => ψ s (g * (k : AdelicGL2 (𝓞 F) F)))
    (fun k => (hψhol _).continuous) s₀ ?_
  filter_upwards [hP s₀] with s hs
  have hrw : (fun k : ↥(archRowIsometrySubgroup F w) => ψ s (g * (k : AdelicGL2 (𝓞 F) F))) =
      (P s)⁻¹ • fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F)) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    exact psi_eq_inv_mul hfac hs _
  rw [hrw]
  exact W.smul_mem _ (hφW s g)

private theorem telescope_quotient (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
    (hφf : ∀ s, IsKfSmooth F (φ s))
    (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    (hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
    (hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
    (hP : ∀ s : ℂ, ∀ᶠ t in 𝓝[≠] s, P t ≠ 0) (hfac : ∀ s g, φ s g = P s * ψ s g)
    (hψhol : ∀ g, Differentiable ℂ fun s => ψ s g) :
    (∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s)) ∧
      (∀ s, IsArchKFinite F (ψ s)) ∧ (∀ s, IsKfSmooth F (ψ s)) ∧
      ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W := by
  obtain ⟨K', hK'o, hK'⟩ :=
    exists_isOpen_subgroup_forall_apply_mul_eq_of_isKfSmooth_of_continuous_of_differentiable
      F φ hφf hφjc hφhol
  refine ⟨fun s => isInducedSection_quotient μ ν α hα hφ hP hfac hψhol s, fun s w => ?_,
    fun s => isKfSmooth_of_subgroup K' hK'o fun g k hk => forall_apply_mul_eq_quotient hP hfac hψhol K' hK' s g hk,
    fun w => ?_⟩
  · obtain ⟨W, hW, hφW⟩ := hφKu w
    haveI := hW
    exact rightTranslatesSpanFinite_of_forall_mem (archRowIsometrySubgroup F w) (ψ s) W
      (fun g => slice_mem_quotient hP hfac hψhol w W hW hφW s g)
  · obtain ⟨W, hW, hφW⟩ := hφKu w
    exact ⟨W, hW, fun s g => slice_mem_quotient hP hfac hψhol w W hW hφW s g⟩

end Transfer

section Continuation

variable {F : Type} [Field F] [NumberField F]

private theorem isOpen_halfPlane : IsOpen {s : ℂ | (1 / 2 : ℝ) < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private theorem weylIntertwiningIntegral_quotient {P : ℂ → ℂ} {φ ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hfac : ∀ s g, φ s g = P s * ψ s g) (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    letI := adeleBorel (𝓞 F) F
    weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g =
      P s * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g := by
  letI := adeleBorel (𝓞 F) F
  have hφs : φ s = fun x => P s * ψ s x := funext (hfac s)
  rw [hφs]
  unfold weylIntertwiningIntegral
  exact MeasureTheory.integral_const_mul _ _

private theorem norm_localChar_le_one {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ)
    (hν : IsUnitaryChar (𝓞 F) F ν) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    ‖((NumberField.TateGlobal.localChar (μ * ν⁻¹) v u : ℂˣ) : ℂ)‖ ≤ 1 := by
  have h1 : ∀ x, ‖((μ x : ℂˣ) : ℂ)‖ = 1 := hμ
  have h2 : ∀ x, ‖((ν x : ℂˣ) : ℂ)‖ = 1 := hν
  unfold NumberField.TateGlobal.localChar
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_inv_eq_inv_val, norm_mul, norm_inv, h1, h2]
  norm_num

private theorem differentiableOn_integral {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ)
    (hν : IsUnitaryChar (𝓞 F) F ν) (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hrow : letI := adeleBorel (𝓞 F) F
      ∃ (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
        (ϖ : (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
        (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
        ∃ R : ℂ → ℂ, MeromorphicOn R Set.univ ∧ DifferentiableOn ℂ R {s : ℂ | 0 < s.re} ∧
          ∀ s : ℂ, 1 / 2 < s.re →
            (∏' v : {v // v ∉ S},
                (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                  * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
              * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g
            = (∏' v : {v // v ∉ S},
                (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                  * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
              * R s) :
    letI := adeleBorel (𝓞 F) F
    DifferentiableOn ℂ (fun s : ℂ => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g)
      {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  letI := adeleBorel (𝓞 F) F
  obtain ⟨S, ϖ, -, R, -, hRd, hR⟩ := hrow
  have hz1 : ∀ v : {v // v ∉ S},
      ‖((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)‖ ≤ 1 :=
    fun v => norm_localChar_le_one hμ hν v.1 (ϖ v.1)
  obtain ⟨hmult, hEd, hEne⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S
      (fun v => ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)) hz1
  have h2re : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → 1 < (2 * s).re := by
    intro s hs
    have h : (2 * s).re = 2 * s.re := by simp
    linarith
  have h2re' : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → 1 < (2 * s + 1).re := by
    intro s hs
    have h : (2 * s + 1).re = 2 * s.re + 1 := by simp
    linarith
  have hA := hEd.comp (differentiable_id.const_mul (2 : ℂ)).differentiableOn
    (fun s (hs : s ∈ {s : ℂ | (1 / 2 : ℝ) < s.re}) => h2re s hs)
  have hB := hEd.comp ((differentiable_id.const_mul (2 : ℂ)).add_const (1 : ℂ)).differentiableOn
    (fun s (hs : s ∈ {s : ℂ | (1 / 2 : ℝ) < s.re}) => h2re' s hs)
  have hB' := hB.inv fun s (hs : s ∈ {s : ℂ | (1 / 2 : ℝ) < s.re}) => hEne _ (h2re' s hs)
  have hR' : DifferentiableOn ℂ R {s : ℂ | (1 / 2 : ℝ) < s.re} :=
    hRd.mono fun s hs => by
      simp only [Set.mem_setOf_eq] at hs ⊢
      linarith
  refine (hA.mul (hB'.mul hR')).congr fun s hs => ?_
  have hs' : (1 / 2 : ℝ) < s.re := hs
  have h := hR s hs'
  rw [tprod_eq_inv_tprod_inv (hmult _ (h2re s hs')) (hEne _ (h2re s hs')),
    tprod_eq_inv_tprod_inv (hmult _ (h2re' s hs')) (hEne _ (h2re' s hs'))] at h
  exact (inv_mul_eq_iff_eq_mul₀ (hEne _ (h2re s hs'))).1 h

private theorem exists_continuation_quotient {P : ℂ → ℂ} {φ ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hPd : Differentiable ℂ P) (hP : ∀ s : ℂ, ∀ᶠ t in 𝓝[≠] s, P t ≠ 0) (hfac : ∀ s g, φ s g = P s * ψ s g)
    (Mc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hMc : ∀ g : AdelicGL2 (𝓞 F) F,
      (letI := adeleBorel (𝓞 F) F
       MeromorphicNFOn (fun s : ℂ => Mc s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
          Mc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g))
    (hI : ∀ g : AdelicGL2 (𝓞 F) F, letI := adeleBorel (𝓞 F) F
      DifferentiableOn ℂ (fun s : ℂ => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g)
        {s : ℂ | (1 / 2 : ℝ) < s.re}) :
    ∃ Mcψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ, ∀ g : AdelicGL2 (𝓞 F) F,
      (letI := adeleBorel (𝓞 F) F
       MeromorphicNFOn (fun s : ℂ => Mcψ s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
          Mcψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g) := by
  letI := adeleBorel (𝓞 F) F
  refine ⟨fun s g => toMeromorphicNFOn (fun t : ℂ => Mc t g / P t) Set.univ s, fun g => ?_⟩
  have hmero : MeromorphicOn (fun t : ℂ => Mc t g / P t) Set.univ := fun t ht =>
    ((hMc g).1.meromorphicOn t ht).div (hPd.analyticAt t).meromorphicAt
  have hNF : MeromorphicNFOn (toMeromorphicNFOn (fun t : ℂ => Mc t g / P t) Set.univ) Set.univ :=
    meromorphicNFOn_toMeromorphicNFOn _ _
  refine ⟨hNF, fun s hs => ?_⟩
  have hIa : AnalyticAt ℂ (fun t : ℂ => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ t) g) s :=
    (hI g).analyticAt (isOpen_halfPlane.mem_nhds hs)
  refine MeromorphicNFAt.apply_eq_of_eventuallyEq_nhdsNE (hNF (Set.mem_univ s)) hIa.meromorphicNFAt ?_
  have h1 : toMeromorphicNFOn (fun t : ℂ => Mc t g / P t) Set.univ =ᶠ[𝓝[≠] s] fun t : ℂ => Mc t g / P t :=
    hmero.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ s)
  refine h1.trans ?_
  have h2 : ∀ᶠ t in 𝓝[≠] s, (1 / 2 : ℝ) < t.re :=
    eventually_nhdsWithin_of_eventually_nhds (isOpen_halfPlane.eventually_mem hs)
  filter_upwards [hP s, h2] with t htP ht
  show Mc t g / P t = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ t) g
  rw [(hMc g).2 t ht, weylIntertwiningIntegral_quotient hfac t g, mul_div_cancel_left₀ _ htP]

private theorem exists_forall_norm_le_norm_mul {B : Set ℂ} (hB : IsCompact B) (hB0 : ∀ s ∈ B, 0 ≤ s.re)
    (Mc : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (hMcNF : ∀ k, MeromorphicNFOn (fun s : ℂ => Mc s k) Set.univ)
    (lam : ℂ → ℂ) (hlam : Differentiable ℂ lam) (P : ℂ → ℂ) (hPd : Differentiable ℂ P)
    {U : Set ℂ} (hU : IsOpen U) (hU0 : {s : ℂ | 0 ≤ s.re} ⊆ U) (H : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hHa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s : ℂ => H s g) U)
    (hHc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) (U ×ˢ Set.univ))
    (hid : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ k, lam s * Mc s k = P s * H s k) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ s ∈ B, ∀ k ∈ adelicMaximalCompact F, ‖lam s * Mc s k‖ ≤ ‖P s‖ * Bd := by
  have hBU : B ⊆ U := fun s hs => hU0 (hB0 s hs)
  have hK : IsCompact (B ×ˢ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F))) :=
    hB.prod (isCompact_adelicMaximalCompact F)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hHc.mono (Set.prod_mono hBU (Set.subset_univ _)))
  refine ⟨max C 0, le_max_right _ _, fun s hs k hk => ?_⟩
  have hsU : s ∈ U := hBU hs
  have hHk : ‖H s k‖ ≤ max C 0 := le_trans (hC (s, k) (Set.mk_mem_prod hs hk)) (le_max_left _ _)
  by_cases hA : AnalyticAt ℂ (fun t : ℂ => Mc t k) s
  ·
    set Ω : Set ℂ := connectedComponentIn U s with hΩ
    have hΩo : IsOpen Ω := hU.connectedComponentIn
    have hΩc : IsPreconnected Ω := isPreconnected_connectedComponentIn
    have hsΩ : s ∈ Ω := mem_connectedComponentIn hsU
    have hhalf : {t : ℂ | 0 ≤ t.re} ⊆ Ω :=
      (convex_halfSpace_re_ge (0 : ℝ)).isPreconnected.subset_connectedComponentIn (hB0 s hs) hU0
    have h1Ω : (1 : ℂ) ∈ Ω := hhalf (by simp)
    have hf : MeromorphicOn (fun t : ℂ => lam t * Mc t k) Ω := fun t _ =>
      (hlam.analyticAt t).meromorphicAt.mul ((hMcNF k).meromorphicOn t (Set.mem_univ t))
    have hh : AnalyticOnNhd ℂ (fun t : ℂ => P t * H t k) Ω := fun t ht =>
      (hPd.analyticAt t).mul (hHa k t (connectedComponentIn_subset U s ht))
    have hfx : AnalyticAt ℂ (fun t : ℂ => lam t * Mc t k) s := (hlam.analyticAt s).mul hA
    have hV : IsOpen (Ω ∩ {t : ℂ | (1 / 2 : ℝ) < t.re}) := hΩo.inter isOpen_halfPlane
    have hVne : (Ω ∩ {t : ℂ | (1 / 2 : ℝ) < t.re}).Nonempty := ⟨1, h1Ω, by norm_num⟩
    have heq : Set.EqOn (fun t : ℂ => lam t * Mc t k) (fun t : ℂ => P t * H t k)
        (Ω ∩ {t : ℂ | (1 / 2 : ℝ) < t.re}) := fun t ht => hid t ht.2 k
    have hval := MeromorphicOn.apply_eq_of_eqOn_of_analyticAt hΩo hΩc hf hh hV hVne Set.inter_subset_left heq
      hsΩ hfx
    rw [hval, norm_mul]
    exact mul_le_mul_of_nonneg_left hHk (norm_nonneg _)
  · have h0 : Mc s k = 0 := MeromorphicNFAt.apply_eq_zero_of_not_analyticAt ((hMcNF k) (Set.mem_univ s)) hA
    rw [h0, mul_zero, norm_zero]
    exact mul_nonneg (norm_nonneg _) (le_max_right _ _)

end Continuation

section Assembly

variable {F : Type} [Field F] [NumberField F]

private theorem weylIntertwiningIntegral_zero_section {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} (hzero : ∀ s g, φ s g = 0)
    (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    letI := adeleBorel (𝓞 F) F
    weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g = 0 := by
  letI := adeleBorel (𝓞 F) F
  have hφs : φ s = fun _ => (0 : ℂ) := funext (hzero s)
  rw [hφs]
  unfold weylIntertwiningIntegral
  simp

private theorem isCompact_box (σ₀ T₀ : ℝ) : IsCompact (Complex.reProdIm (Set.Icc 0 σ₀) (Set.Icc (-T₀) T₀)) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    ((Metric.isBounded_Icc 0 σ₀).reProdIm (Metric.isBounded_Icc (-T₀) T₀))

private theorem mem_box {σ₀ T₀ : ℝ} {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ σ₀) (h2 : |s.im| ≤ T₀) :
    s ∈ Complex.reProdIm (Set.Icc 0 σ₀) (Set.Icc (-T₀) T₀) :=
  Complex.mem_reProdIm.2 ⟨⟨h0, h1⟩, abs_le.1 h2⟩

private theorem re_nonneg_of_mem_box {σ₀ T₀ : ℝ} {s : ℂ}
    (hs : s ∈ Complex.reProdIm (Set.Icc 0 σ₀) (Set.Icc (-T₀) T₀)) : 0 ≤ s.re :=
  (Complex.mem_reProdIm.1 hs).1.1

private theorem exists_mem_adelicMaximalCompact_ne_zero {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ} {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)} {χ : AdelicGL2 (𝓞 F) F → ℂ} {s : ℂ}
    (hχ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) χ) {g : AdelicGL2 (𝓞 F) F}
    (hg : χ g ≠ 0) : ∃ k ∈ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)), χ k ≠ 0 := by
  obtain ⟨b, k, hb, hkfin, hkarch, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  refine ⟨k, mem_adelicMaximalCompact_iff.2 ⟨hkfin, hkarch⟩, fun hk => hg ?_⟩
  rw [hχ b hb k, hk, mul_zero]

private theorem exists_bound_clause (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
    (hφf : ∀ s, IsKfSmooth F (φ s))
    (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    (hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
    (hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
    (Mc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hMc : ∀ g : AdelicGL2 (𝓞 F) F,
      (letI := adeleBorel (𝓞 F) F
       MeromorphicNFOn (fun s : ℂ => Mc s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
          Mc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g))
    (lam : ℂ → ℂ) (hlam : Differentiable ℂ lam)
    (hN1H : ∀ (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s)) →
      (∀ s, IsArchKFinite F (ψ s)) → (∀ s, IsKfSmooth F (ψ s)) →
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2) → (∀ g, Differentiable ℂ (fun s => ψ s g)) →
      (∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) →
      ∀ Mcψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
        (∀ g : AdelicGL2 (𝓞 F) F,
          (letI := adeleBorel (𝓞 F) F
           MeromorphicNFOn (fun s : ℂ => Mcψ s g) Set.univ ∧
            ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
              Mcψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g)) →
        ∃ U : Set ℂ, IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
          ∃ H : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
            (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s : ℂ => H s g) U) ∧
            ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) (U ×ˢ Set.univ) ∧
            ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F, H s g = lam s * Mcψ s g)
    (hEuler : ∀ (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s)) →
      (∀ s, IsArchKFinite F (ψ s)) → (∀ s, IsKfSmooth F (ψ s)) →
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2) → (∀ g, Differentiable ℂ (fun s => ψ s g)) →
      ∀ g : AdelicGL2 (𝓞 F) F,
        letI := adeleBorel (𝓞 F) F
        ∃ (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
          (ϖ : (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
          (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
          ∃ R : ℂ → ℂ, MeromorphicOn R Set.univ ∧ DifferentiableOn ℂ R {s : ℂ | 0 < s.re} ∧
            ∀ s : ℂ, 1 / 2 < s.re →
              (∏' v : {v // v ∉ S},
                  (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
                * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g
              = (∏' v : {v // v ∉ S},
                  (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
                * R s)
    (σ₀ T₀ : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ → |s.im| ≤ T₀ →
      ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
        ‖lam s * Mc s k‖ ≤ A * ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖ := by
  letI := adeleBorel (𝓞 F) F
  have hMcNF : ∀ k, MeromorphicNFOn (fun s : ℂ => Mc s k) Set.univ := fun k => (hMc k).1
  by_cases hzero : ∀ s g, φ s g = 0
  ·
    have hid : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ k, lam s * Mc s k = (fun _ : ℂ => (0 : ℂ)) s * (0 : ℂ) := by
      intro s hs k
      rw [(hMc k).2 s hs, weylIntertwiningIntegral_zero_section hzero s k]
      simp
    obtain ⟨Bd, -, hBd⟩ := exists_forall_norm_le_norm_mul (isCompact_box σ₀ T₀) (fun s hs => re_nonneg_of_mem_box hs)
      Mc hMcNF lam hlam (fun _ => (0 : ℂ)) (differentiable_const _) isOpen_univ (Set.subset_univ _)
      (fun _ _ => (0 : ℂ)) (fun _ => analyticOnNhd_const) continuousOn_const hid
    refine ⟨0, le_rfl, fun s h0 h1 h2 k hk => ?_⟩
    have h := hBd s (mem_box h0 h1 h2) k hk
    simp only [norm_zero, zero_mul] at h
    rw [zero_mul]
    exact h
  · push Not at hzero
    obtain ⟨P, ψ, hPd, hP, hψjc, hψhol, hfac, hbox⟩ :=
      EntireFamilyDivision.exists_divisor_family hφjc hφhol (isCompact_box σ₀ T₀) hzero
    obtain ⟨hψ, hψK, hψf, hψKu⟩ := telescope_quotient μ ν α hα hφ hφf hφjc hφhol hφKu hP hfac hψhol
    have hI : ∀ g : AdelicGL2 (𝓞 F) F,
        DifferentiableOn ℂ (fun s : ℂ => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g)
          {s : ℂ | (1 / 2 : ℝ) < s.re} :=
      fun g => differentiableOn_integral hμ hν ψ g (hEuler ψ hψ hψK hψf hψjc hψhol g)
    obtain ⟨Mcψ, hMcψ⟩ := exists_continuation_quotient hPd hP hfac Mc hMc hI
    obtain ⟨U, hU, hU0, H, hHa, hHc, hH⟩ := hN1H ψ hψ hψK hψf hψjc hψhol hψKu Mcψ hMcψ
    have hid : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ k, lam s * Mc s k = P s * H s k := by
      intro s hs k
      rw [hH s hs k, (hMcψ k).2 s hs, (hMc k).2 s hs, weylIntertwiningIntegral_quotient hfac s k]
      ring
    obtain ⟨Bd, hBd0, hBd⟩ := exists_forall_norm_le_norm_mul (isCompact_box σ₀ T₀)
      (fun s hs => re_nonneg_of_mem_box hs) Mc hMcNF lam hlam P hPd hU hU0 H hHa hHc hid
    have hpos : ∀ s ∈ Complex.reProdIm (Set.Icc 0 σ₀) (Set.Icc (-T₀) T₀),
        ∃ k ∈ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)), ψ s k ≠ 0 := by
      intro s hs
      obtain ⟨g, hg⟩ := hbox s hs
      exact exists_mem_adelicMaximalCompact_ne_zero (hψ s) hg
    obtain ⟨c, hc0, hc⟩ :=
      exists_pos_forall_le_iSup_norm (isCompact_adelicMaximalCompact F) hψjc (isCompact_box σ₀ T₀) hpos
    refine ⟨Bd / c, div_nonneg hBd0 hc0.le, fun s h0 h1 h2 k hk => ?_⟩
    have hsB := mem_box h0 h1 h2
    have hsup : (⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) =
        ‖P s‖ * ⨆ k' : ↥(adelicMaximalCompact F), ‖ψ s (k' : AdelicGL2 (𝓞 F) F)‖ := by
      rw [Real.mul_iSup_of_nonneg (norm_nonneg _)]
      simp only [hfac, norm_mul]
    rw [hsup]
    calc ‖lam s * Mc s k‖ ≤ ‖P s‖ * Bd := hBd s hsB k hk
      _ = Bd / c * (‖P s‖ * c) := by field_simp
      _ ≤ Bd / c * (‖P s‖ * ⨆ k' : ↥(adelicMaximalCompact F), ‖ψ s (k' : AdelicGL2 (𝓞 F) F)‖) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hBd0 hc0.le)
        exact mul_le_mul_of_nonneg_left (hc s hsB) (norm_nonneg _)

end Assembly

end QuotientSectionFamily

open scoped Classical in

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Mc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ g : AdelicGL2 (𝓞 F) F,
        (letI := adeleBorel (𝓞 F) F
         MeromorphicNFOn (fun s : ℂ => Mc s g) Set.univ ∧
          ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
            Mc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g))
      (σ₀ : ℝ) (_hσ₀ : 0 < σ₀),
    (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
      ∀ Q : ℂ → ℂ, Differentiable ℂ Q →
        (∀ w : ℂ, 1 < w.re → Q w = (w - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
          ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
              v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))},
            (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v.1 then
                    (((μ * ν⁻¹) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∀ T₀ : ℝ, ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ → |s.im| ≤ T₀ →
          ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
            ‖(s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * Q (2 * s + 1) * Mc s k‖ ≤
              A * ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) ∧
    ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
      ∀ L : ℂ → ℂ, Differentiable ℂ L →
        (∀ w : ℂ, 1 < w.re → L w =
          ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
              v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))},
            (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v.1 then
                    (((μ * ν⁻¹) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∀ T₀ : ℝ, ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ → |s.im| ≤ T₀ →
          ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
            ‖L (2 * s + 1) * Mc s k‖ ≤
              A * ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) := by
  intro α hα μ ν hμ hν hμic hνic φ hφ hφK hφf hφjc hφhol hμc hνc hφKu Mc hMc σ₀ _hσ₀
  have hEuler := fun (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (hψ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      (hψK : ∀ s, IsArchKFinite F (ψ s)) (hψf : ∀ s, IsKfSmooth F (ψ s))
      (hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2))
      (hψhol : ∀ g, Differentiable ℂ (fun s => ψ s g)) (g : AdelicGL2 (𝓞 F) F) =>
    AutomorphicForm.exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul F hα μ ν hμ hν
      ψ hψ hψK hψf hψjc hψhol g
  have hN1H := fun (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (hψ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      (hψK : ∀ s, IsArchKFinite F (ψ s)) (hψf : ∀ s, IsKfSmooth F (ψ s))
      (hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2))
      (hψhol : ∀ g, Differentiable ℂ (fun s => ψ s g))
      (hψKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Mcψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (hMcψ : ∀ g : AdelicGL2 (𝓞 F) F,
        (letI := adeleBorel (𝓞 F) F
         MeromorphicNFOn (fun s : ℂ => Mcψ s g) Set.univ ∧
          ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
            Mcψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g)) =>
    AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation F hα μ ν
      hμ hν hμic hνic ψ hψ hψK hψf hψjc hψhol hμc hνc hψKu Mcψ hMcψ
  refine ⟨fun τ hτ Q hQd hQprod T₀ => ?_, fun hne L hLd hLprod T₀ => ?_⟩
  · refine QuotientSectionFamily.exists_bound_clause α hα μ ν hμ hν φ hφ hφf hφjc hφhol hφKu Mc hMc
      (fun s : ℂ => (s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * Q (2 * s + 1))
      ((differentiable_id.sub_const _).mul (hQd.comp ((differentiable_id.const_mul (2 : ℂ)).add_const 1)))
      (fun ψ hψ hψK hψf hψjc hψhol hψKu Mcψ hMcψ => ?_) hEuler σ₀ T₀
    obtain ⟨U, hU, hU0, H, hHa, hHc, hH⟩ := (hN1H ψ hψ hψK hψf hψjc hψhol hψKu Mcψ hMcψ).1 τ hτ Q hQd hQprod
    refine ⟨U, hU, hU0, H, hHa, hHc, fun s hs g => ?_⟩
    rw [hH s hs g]
    ring
  · exact QuotientSectionFamily.exists_bound_clause α hα μ ν hμ hν φ hφ hφf hφjc hφhol hφKu Mc hMc
      (fun s : ℂ => L (2 * s + 1)) (hLd.comp ((differentiable_id.const_mul (2 : ℂ)).add_const 1))
      (fun ψ hψ hψK hψf hψjc hψhol hψKu Mcψ hMcψ =>
        (hN1H ψ hψ hψK hψf hψjc hψhol hψKu Mcψ hMcψ).2 hne L hLd hLprod) hEuler σ₀ T₀

end S_AutomorphicForm_exists_norm_eulerProduct_mul_intertwining_le_mul_of_abs_im_le_of_isInducedSection
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_eulerProduct_mul_intertwining_le_mul_of_abs_im_le_of_isInducedSection (solution)
