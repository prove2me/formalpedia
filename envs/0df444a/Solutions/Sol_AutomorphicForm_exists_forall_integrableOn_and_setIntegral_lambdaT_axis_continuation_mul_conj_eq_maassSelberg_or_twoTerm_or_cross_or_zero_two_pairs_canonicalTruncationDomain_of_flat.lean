-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_canonicalTruncationDomain_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0328f40c-4128-55f1-aaf9-c9678207a3c6

import Mathlib
import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_and_eq_cross_and_eq_zero_two_pairs_slab_of_ne
import Theorems.Thm_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
import Theorems.Thm_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_canonicalTruncationDomain_of_flat
p2m_attr_erase "instance" "FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions"
p2m_attr_erase "instance" "instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv"
p2m_attr_erase "simp" "LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.TateLocal.conductorExponentAt_one SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
open AutomorphicForm
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section
namespace UnitAux

theorem eq_zero_of_continuousAt_of_norm_le_mul_abs_sub {N : ℝ → ℂ} {t M : ℝ}
    (hN : ContinuousAt N t) (hle : ∀ᶠ t' in nhdsWithin t {t}ᶜ, ‖N t'‖ ≤ M * |t' - t|) : N t = 0 := by
  have h1 : Filter.Tendsto (fun t' => ‖N t'‖) (nhdsWithin t {t}ᶜ) (nhds ‖N t‖) :=
    (hN.norm.tendsto).mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun t' : ℝ => M * |t' - t|) (nhdsWithin t {t}ᶜ) (nhds 0) := by
    have : Filter.Tendsto (fun t' : ℝ => M * |t' - t|) (nhds t) (nhds (M * |t - t|)) :=
      ((continuous_const.mul ((continuous_id.sub continuous_const).abs)).tendsto t)
    rw [sub_self, abs_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h3 : ‖N t‖ ≤ 0 := le_of_tendsto_of_tendsto h1 h2 hle
  exact norm_le_zero_iff.mp h3

theorem continuous_integral_of_continuous {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (μ : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure μ]
    {f : ℝ → Y → ℂ} (hf : Continuous fun p : ℝ × Y => f p.1 p.2) :
    Continuous fun x => ∫ y, f x y ∂μ := by
  have hf' : Continuous f.uncurry := hf
  have := continuous_parametric_integral_of_continuous (μ := μ) hf' (isCompact_univ (X := Y))
  simpa [MeasureTheory.setIntegral_univ] using this

end UnitAux
end

noncomputable section
namespace AxisAux

theorem tendsto_div_of_hasDerivAt {N : ℝ → ℂ} {N' : ℂ} {t : ℝ} (hN : HasDerivAt N N' t) (h0 : N t = 0) :
    Filter.Tendsto (fun t' : ℝ => N t' / (Complex.I * (((t : ℂ)) - (t' : ℂ)))) (nhdsWithin t {t}ᶜ)
      (nhds (-N' / Complex.I)) := by

  have hs := hN.tendsto_slope_zero

  have key : ∀ t' : ℝ, t' ≠ t →
      N t' / (Complex.I * ((t : ℂ) - (t' : ℂ))) = (-1 / Complex.I) * ((t' - t : ℝ)⁻¹ • (N (t + (t' - t)) - N t)) := by
    intro t' ht'
    have hne : ((t' : ℂ) - (t : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ht')
    rw [h0, sub_zero, add_sub_cancel, Complex.real_smul]
    push_cast
    field_simp [Complex.I_ne_zero, hne, sub_ne_zero.mpr (Ne.symm (by exact_mod_cast ht' : (t':ℂ) ≠ t))]
    ring
  have h1 : Filter.Tendsto (fun t' : ℝ => (t' - t : ℝ)⁻¹ • (N (t + (t' - t)) - N t)) (nhdsWithin t {t}ᶜ) (nhds N') := by
    have hmap : Filter.Tendsto (fun t' : ℝ => t' - t) (nhdsWithin t {t}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Filter.Tendsto (fun t' : ℝ => t' - t) (nhds t) (nhds 0) := by
          rw [show (0 : ℝ) = t - t by simp]
          exact (continuous_sub_right t).continuousAt
        exact this.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun t' ht' => sub_ne_zero.mpr ht'
    exact hs.comp hmap
  have h2 := h1.const_mul (-1 / Complex.I)
  have heq : (fun t' : ℝ => (-1 / Complex.I) * ((t' - t : ℝ)⁻¹ • (N (t + (t' - t)) - N t))) =ᶠ[nhdsWithin t {t}ᶜ]
      (fun t' : ℝ => N t' / (Complex.I * ((t : ℂ) - (t' : ℂ)))) :=
    eventually_nhdsWithin_of_forall fun t' ht' => (key t' ht').symm
  have hlim : (-1 / Complex.I) * N' = -N' / Complex.I := by field_simp
  rw [← hlim]
  exact h2.congr' heq

end AxisAux
end

noncomputable section
namespace AxisAux
open MeasureTheory
open scoped ComplexConjugate

theorem hasDerivAt_integral_mul_conj_axis {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    (a : Y → ℂ) (ha : Continuous a) (G : ℂ → Y → ℂ) (O : Set ℂ) (hO : IsOpen O)
    (hGa : ∀ y, AnalyticOnNhd ℂ (fun s => G s y) O) (hGc : ContinuousOn (fun p : ℂ × Y => G p.1 p.2) (O ×ˢ Set.univ))
    (t : ℝ) (ht : ((t : ℂ) * Complex.I) ∈ O) :
    HasDerivAt (fun t' : ℝ => ∫ y, a y * conj (G ((t' : ℂ) * Complex.I) y) ∂μ)
      (∫ y, a y * conj (deriv (fun s => G s y) ((t : ℂ) * Complex.I) * Complex.I) ∂μ) t := by

  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO _ ht
  set r : ℝ := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hcb : Metric.closedBall ((t : ℂ) * Complex.I) (2 * r) ⊆ O := fun w hw =>
    hball (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by simp only [hr]; linarith)))

  have hK : IsCompact (Metric.closedBall ((t : ℂ) * Complex.I) (2 * r) ×ˢ (Set.univ : Set Y)) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hGc.mono (Set.prod_mono hcb le_rfl))
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ p ∈ Metric.closedBall ((t : ℂ) * Complex.I) (2 * r) ×ˢ (Set.univ : Set Y), ‖G p.1 p.2‖ ≤ C :=
    fun p hp => (hC₀ p hp).trans (le_max_left _ _)

  have hdist_ax : ∀ t' : ℝ, dist ((t' : ℂ) * Complex.I) ((t : ℂ) * Complex.I) = |t' - t| := by
    intro t'
    rw [Complex.dist_eq, ← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  have hax' : ∀ t' : ℝ, t' ∈ Metric.ball t r →
      Metric.closedBall ((t' : ℂ) * Complex.I) r ⊆ Metric.closedBall ((t : ℂ) * Complex.I) (2 * r) := by
    intro t' ht' w hw
    rw [Metric.mem_closedBall]
    have h1 : dist w ((t' : ℂ) * Complex.I) ≤ r := Metric.mem_closedBall.mp hw
    have h2 : dist ((t' : ℂ) * Complex.I) ((t : ℂ) * Complex.I) < r := by
      rw [hdist_ax, ← Real.dist_eq]; exact Metric.mem_ball.mp ht'
    linarith [dist_triangle w ((t' : ℂ) * Complex.I) ((t : ℂ) * Complex.I)]
  have hmemO : ∀ t' : ℝ, t' ∈ Metric.ball t r → ((t' : ℂ) * Complex.I) ∈ O := fun t' ht' =>
    hcb (hax' t' ht' (Metric.mem_closedBall_self hr0.le))

  have hderiv_le : ∀ (y : Y) (t' : ℝ), t' ∈ Metric.ball t r →
      ‖deriv (fun s => G s y) ((t' : ℂ) * Complex.I)‖ ≤ C / r := by
    intro y t' ht'
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 ?_ ?_
    · refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ hr0.ne']
      exact ((hGa y).differentiableOn).mono ((hax' t' ht').trans hcb)
    · intro w hw
      exact hC (w, y) ⟨hax' t' ht' (Metric.sphere_subset_closedBall hw), Set.mem_univ _⟩

  have hcont_y : ∀ s ∈ O, Continuous fun y => G s y := fun s hs =>
    (hGc.comp_continuous (continuous_const.prodMk continuous_id) fun y => ⟨hs, Set.mem_univ _⟩)

  have hpt : ∀ (y : Y) (t' : ℝ), t' ∈ Metric.ball t r →
      HasDerivAt (fun u : ℝ => a y * conj (G ((u : ℂ) * Complex.I) y))
        (a y * conj (deriv (fun s => G s y) ((t' : ℂ) * Complex.I) * Complex.I)) t' := by
    intro y t' ht'
    have hd : DifferentiableAt ℂ (fun s => G s y) ((t' : ℂ) * Complex.I) :=
      (hGa y).differentiableOn.differentiableAt (hO.mem_nhds (hmemO t' ht'))
    have h1 : HasDerivAt (fun w : ℂ => G (w * Complex.I) y) (deriv (fun s => G s y) ((t' : ℂ) * Complex.I) * Complex.I) (t' : ℂ) := by
      have := hd.hasDerivAt.comp (t' : ℂ) ((hasDerivAt_id (t' : ℂ)).mul_const Complex.I)
      first | simpa using this | (have h_1 := this; simp at h_1; exact h_1) | (have h_1 := this; simp at h_1 ⊢; exact h_1) | exact (this)
    have h2 : HasDerivAt (fun u : ℝ => G ((u : ℂ) * Complex.I) y) (deriv (fun s => G s y) ((t' : ℂ) * Complex.I) * Complex.I) t' :=
      h1.comp_ofReal
    have h3 : HasDerivAt (fun u : ℝ => conj (G ((u : ℂ) * Complex.I) y))
        (conj (deriv (fun s => G s y) ((t' : ℂ) * Complex.I) * Complex.I)) t' := by
      have := (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t' h2)
      first | simpa using this | (have h_1 := this; simp at h_1; exact h_1) | (have h_1 := this; simp at h_1 ⊢; exact h_1) | exact (this)
    exact h3.const_mul (a y)

  have hF'meas : AEStronglyMeasurable (fun y => a y * conj (deriv (fun s => G s y) ((t : ℂ) * Complex.I) * Complex.I)) μ := by
    set h : ℕ → ℂ := fun n => (((r * (1 / ((n : ℝ) + 1)) : ℝ)) : ℂ) with hh
    have hhpos : ∀ n : ℕ, (0 : ℝ) < r * (1 / ((n : ℝ) + 1)) := fun n => mul_pos hr0 (Nat.one_div_pos_of_nat)
    have hhne : ∀ n : ℕ, h n ≠ 0 := fun n => by simp only [hh]; exact_mod_cast (hhpos n).ne'
    have hseq : ∀ y, Filter.Tendsto (fun n : ℕ => (h n)⁻¹ • (G ((t : ℂ) * Complex.I + h n) y - G ((t : ℂ) * Complex.I) y))
        Filter.atTop (nhds (deriv (fun s => G s y) ((t : ℂ) * Complex.I))) := by
      intro y
      have hd : HasDerivAt (fun s => G s y) (deriv (fun s => G s y) ((t : ℂ) * Complex.I)) ((t : ℂ) * Complex.I) :=
        ((hGa y).differentiableOn.differentiableAt (hO.mem_nhds ht)).hasDerivAt
      have hs := hd.tendsto_slope_zero
      have hu : Filter.Tendsto h Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Filter.Eventually.of_forall hhne)
        have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul r
        rw [mul_zero] at h1
        have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h1
        rw [Complex.ofReal_zero] at h2
        exact h2
      exact hs.comp hu

    have hmem_n : ∀ n : ℕ, ((t : ℂ) * Complex.I + h n) ∈ O := by
      intro n
      refine hcb (Metric.mem_closedBall.mpr ?_)
      rw [dist_eq_norm, add_sub_cancel_left, hh, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hhpos n)]
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (Nat.cast_add_one_pos n)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      nlinarith
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (f := fun n y => a y * conj ((h n)⁻¹ • (G ((t : ℂ) * Complex.I + h n) y - G ((t : ℂ) * Complex.I) y) * Complex.I))
      (fun n => ?_) ?_
    · exact (ha.fun_mul (Complex.continuous_conj.comp ((((hcont_y _ (hmem_n n)).fun_sub (hcont_y _ ht)).fun_const_smul _).fun_mul
        continuous_const))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y =>
        ((Complex.continuous_conj.tendsto _).comp (((hseq y).mul_const Complex.I))).const_mul (a y)

  have hFcont : ∀ u : ℝ, u ∈ Metric.ball t r → Continuous fun y => a y * conj (G ((u : ℂ) * Complex.I) y) := fun u hu =>
    ha.mul (Complex.continuous_conj.comp (hcont_y _ (hmemO u hu)))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := μ) (x₀ := t) (s := Metric.ball t r)
    (F := fun (u : ℝ) y => a y * conj (G ((u : ℂ) * Complex.I) y))
    (F' := fun (u : ℝ) y => a y * conj (deriv (fun s => G s y) ((u : ℂ) * Complex.I) * Complex.I))
    (bound := fun y => ‖a y‖ * (C / r))
    (Metric.ball_mem_nhds t hr0)
    (by
      filter_upwards [Metric.ball_mem_nhds t hr0] with u hu
      exact (hFcont u hu).aestronglyMeasurable)
    ((hFcont t (Metric.mem_ball_self hr0)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hF'meas
    (Filter.Eventually.of_forall fun y u hu => by
      rw [norm_mul, Complex.norm_conj, norm_mul, Complex.norm_I, mul_one]
      exact mul_le_mul_of_nonneg_left (hderiv_le y u hu) (norm_nonneg _))
    ((ha.norm.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall fun y u hu => hpt y u hu)
  exact hmain.2

end AxisAux
end

theorem solution
    (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L)) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ cMS : ℝ, 0 < cMS ∧ ∃ R₀ : ℝ,
    ∀ (μ ν μ' ν' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 L) L μ) (_hν : IsUnitaryChar (𝓞 L) L ν)
      (_hμ' : IsUnitaryChar (𝓞 L) L μ') (_hν' : IsUnitaryChar (𝓞 L) L ν')
      (_hμF : IsIdeleClassChar (𝓞 L) L μ) (_hνF : IsIdeleClassChar (𝓞 L) L ν)
      (_hμ'F : IsIdeleClassChar (𝓞 L) L μ') (_hν'F : IsIdeleClassChar (𝓞 L) L ν')
      (_hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hμ'k : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ' x : ℂˣ) : ℂ))
      (_hν'k : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν' x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite L (φf s))
      (_hφff : ∀ s, IsKfSmooth L (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => φf s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
        φf s (k : AdelicGL2 (𝓞 L) L) = φf 0 (k : AdelicGL2 (𝓞 L) L))
      (ψf : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ' αm hαm s) (etaSnd ν' αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite L (ψf s))
      (_hψff : ∀ s, IsKfSmooth L (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => ψf s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hψflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
        ψf s (k : AdelicGL2 (𝓞 L) L) = ψf 0 (k : AdelicGL2 (𝓞 L) L))
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eφ s g = φf s g + ∑' ξ : L, φf s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nφ s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eψ s g = ψf s g + ∑' ξ : L, ψf s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nψ s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (ψf s) g))
      (t : ℝ) (R : ℝ) (_hR : R₀ ≤ R),
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (Eφ ((t : ℂ) * Complex.I))
          x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (Eψ ((t : ℂ) * Complex.I))
          x))
        (AutomorphicForm.canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (μ' = μ → ν' = ν → μ = ν → t ≠ 0 →
        (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eψ ((t : ℂ) * Complex.I))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) * (2 * (R : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L))
            + (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ)) )) ∧
      (μ' = μ → ν' = ν → (∃ z ∈ NumberField.TateGlobal.normOneIdeles L, μ z ≠ ν z) → t ≠ 0 →
        (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eψ ((t : ℂ) * Complex.I))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) * (2 * (R : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) )) ∧
      (μ' = ν → ν' = μ → (∃ z ∈ NumberField.TateGlobal.normOneIdeles L, μ z ≠ ν z) → t ≠ 0 →
        (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eψ ((t : ℂ) * Complex.I))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ)) )) ∧
      ((∃ z ∈ NumberField.TateGlobal.normOneIdeles L, μ' z ≠ μ z ∨ ν' z ≠ ν z) →
        (∃ z ∈ NumberField.TateGlobal.normOneIdeles L, μ' z ≠ ν z ∨ ν' z ≠ μ z) →
        (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eψ ((t : ℂ) * Complex.I))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = 0) := by
  intro αm hαm

  obtain ⟨c, hc, R₀, hMS⟩ := AutomorphicForm.exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_and_eq_cross_and_eq_zero_two_pairs_slab_of_ne L α β hα hαβ ΦL hαm
  refine ⟨c, hc, R₀, ?_⟩
  intro μ ν μ' ν' hμ hν hμ' hν' hμF hνF hμ'F hν'F hμk hνk hμ'k hν'k
    φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflat ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflat
    Oφ Eφ Nφ hEφ Oψ Eψ Nψ hEψ t R hR
  obtain ⟨hOψ, hOψc, hOψax, hOψhalf, hEψa, hNψa, hEψjc, hNψjc, hEψE, hNψN⟩ := hEψ
  obtain ⟨hOφ, hOφc, hOφax, hOφhalf, hEφa, hNφa, hEφjc, hNφjc, hEφE, hNφN⟩ := hEφ

  have hBψ := AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family L α β hα hαβ ΦL hαm μ' ν' hμ' hν' hμ'F hν'F hμ'k hν'k
    ψf hψf hψfK hψff hψfjc hψfhol hψfKu Oψ Eψ Nψ hOψ hOψc hOψhalf hEψa hNψa hEψjc hNψjc
    (fun s hs g => by rw [hEψE s hs g, AutomorphicForm.pseudoEisenstein_apply]) hNψN R
  have hBφ := AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family L α β hα hαβ ΦL hαm μ ν hμ hν hμF hνF hμk hνk
    φf hφf hφfK hφff hφfjc hφfhol hφfKu Oφ Eφ Nφ hOφ hOφc hOφhalf hEφa hNφa hEφjc hNφjc
    (fun s hs g => by rw [hEφE s hs g, AutomorphicForm.pseudoEisenstein_apply]) hNφN R

  set vC : ℂ := ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ)) with hvC
  set P1 : ℝ → ℂ := fun b => ∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) *
      conj (ψf ((b : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L) with hP1
  set P2 : ℝ → ℂ := fun b => ∫ k, (vC⁻¹ * Nφ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) *
      conj (vC⁻¹ * Nψ ((b : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L) with hP2
  set P3 : ℝ → ℂ := fun b => ∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) *
      conj (vC⁻¹ * Nψ ((b : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L) with hP3
  set P4 : ℝ → ℂ := fun b => ∫ k, (vC⁻¹ * Nφ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) *
      conj (ψf ((b : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L) with hP4
  set Q : ℂ := ∫ k, (vC⁻¹ * Nφ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) *
      conj (vC⁻¹ * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 L) L)) ((t : ℂ) * Complex.I)) ∂(AutomorphicForm.maximalCompactHaar L) with hQ
  set Lφ : AdelicGL2 (𝓞 L) L → ℂ := fun x => (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))) x with hLφ
  set Lψ : ℝ → AdelicGL2 (𝓞 L) L → ℂ := fun b x => (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eψ ((b : ℂ) * Complex.I))) x with hLψ
  set Ib : ℝ → ℂ := fun b => ∫ x in AutomorphicForm.canonicalTruncationDomain L α β, Lφ x * conj (Lψ b x)
    ∂(adelicGLHaar (Fin 2) (𝓞 L) L) with hIb

  have haxφ : Continuous fun p : ℝ × ↥(adelicMaximalCompact L) => φf ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 L) L) :=
    hφfjc.comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const |>.prodMk
      (continuous_subtype_val.comp continuous_snd))
  have haxψ : Continuous fun p : ℝ × ↥(adelicMaximalCompact L) => ψf ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 L) L) :=
    hψfjc.comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const |>.prodMk
      (continuous_subtype_val.comp continuous_snd))
  have haxNφ : Continuous fun p : ℝ × ↥(adelicMaximalCompact L) => Nφ ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 L) L) := by
    have hmap : Continuous fun p : ℝ × ↥(adelicMaximalCompact L) => (((p.1 : ℂ) * Complex.I), (p.2 : AdelicGL2 (𝓞 L) L)) :=
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk (continuous_subtype_val.comp continuous_snd)
    refine hNφjc.comp_continuous hmap fun p => ⟨hOφax (by simp), Set.mem_univ _⟩
  have haxNψ : Continuous fun p : ℝ × ↥(adelicMaximalCompact L) => Nψ ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 L) L) := by
    have hmap : Continuous fun p : ℝ × ↥(adelicMaximalCompact L) => (((p.1 : ℂ) * Complex.I), (p.2 : AdelicGL2 (𝓞 L) L)) :=
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk (continuous_subtype_val.comp continuous_snd)
    refine hNψjc.comp_continuous hmap fun p => ⟨hOψax (by simp), Set.mem_univ _⟩
  have hP3c : Continuous P3 := by
    simp only [hP3]
    exact UnitAux.continuous_integral_of_continuous _
      ((haxφ.comp (continuous_const.prodMk continuous_snd)).mul
        (Complex.continuous_conj.comp (continuous_const.mul (haxNψ.comp (continuous_fst.prodMk continuous_snd)))))
  have hP4c : Continuous P4 := by
    simp only [hP4]
    exact UnitAux.continuous_integral_of_continuous _
      ((continuous_const.mul (haxNφ.comp (continuous_const.prodMk continuous_snd))).mul
        (Complex.continuous_conj.comp (haxψ.comp (continuous_fst.prodMk continuous_snd))))

  have hP1const : ∀ b : ℝ, P1 b = P1 t := by
    intro b; simp only [hP1]
    congr 1; funext k
    rw [hψflat ((b : ℂ) * Complex.I) k, hψflat ((t : ℂ) * Complex.I) k]

  have hP2d : HasDerivAt P2 (-Complex.I * Q) t := by
    set a : ↥(adelicMaximalCompact L) → ℂ := fun k => vC⁻¹ * Nφ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj vC⁻¹ with ha
    have hac : Continuous a := ((continuous_const.mul (haxNφ.comp (continuous_const.prodMk continuous_id))).mul continuous_const)
    have hG2 := AxisAux.hasDerivAt_integral_mul_conj_axis (AutomorphicForm.maximalCompactHaar L) a hac
      (fun s (k : ↥(adelicMaximalCompact L)) => Nψ s (k : AdelicGL2 (𝓞 L) L)) Oψ hOψ (fun k => hNψa _)
      (hNψjc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
        (fun p hp => ⟨hp.1, Set.mem_univ _⟩)) t (hOψax (by simp))
    have hfun : P2 = fun b : ℝ => ∫ k, a k * conj (Nψ ((b : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L) := by
      funext b; simp only [hP2, ha]; congr 1; funext k; rw [map_mul]; ring
    have hval : (∫ k, a k * conj (deriv (fun s => Nψ s (k : AdelicGL2 (𝓞 L) L)) ((t : ℂ) * Complex.I) * Complex.I)
        ∂(AutomorphicForm.maximalCompactHaar L)) = -Complex.I * Q := by
      simp only [hQ, ha]
      rw [← integral_const_mul]
      congr 1; funext k; rw [map_mul, map_mul, Complex.conj_I]; ring
    rw [hfun, ← hval]
    exact hG2

  have hconjI : ∀ b : ℝ, conj ((b : ℂ) * Complex.I) = -((b : ℂ) * Complex.I) := by
    intro b; rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hsum : ∀ b : ℝ, ((t : ℂ) * Complex.I) + conj ((b : ℂ) * Complex.I) = ((t - b : ℝ) : ℂ) * Complex.I := by
    intro b; rw [hconjI]; push_cast; ring
  have hdiff : ∀ b : ℝ, ((t : ℂ) * Complex.I) - conj ((b : ℂ) * Complex.I) = ((t + b : ℝ) : ℂ) * Complex.I := by
    intro b; rw [hconjI]; push_cast; ring

  set μΦ : MeasureTheory.Measure (AdelicGL2 (𝓞 L) L) :=
    (adelicGLHaar (Fin 2) (𝓞 L) L).restrict (AutomorphicForm.canonicalTruncationDomain L α β) with hμΦ
  have hmemφ : MemLp Lφ 2 μΦ := hBφ.1 _ (hOφax (by simp))
  have hmemψ : ∀ b : ℝ, MemLp (Lψ b) 2 μΦ := fun b => hBψ.1 _ (hOψax (by simp))
  have hmemψc : ∀ b : ℝ, MemLp (fun x => conj (Lψ b x)) 2 μΦ := fun b =>
    (hmemψ b).of_le (Complex.continuous_conj.comp_aestronglyMeasurable (hmemψ b).1)
      (Filter.Eventually.of_forall fun x => by rw [Complex.norm_conj])
  have hint : IntegrableOn (fun x => Lφ x * conj (Lψ t x)) (AutomorphicForm.canonicalTruncationDomain L α β)
      (adelicGLHaar (Fin 2) (𝓞 L) L) := by
    have := hmemφ.integrable_mul (hmemψc t)
    exact this
  have hIlim : Filter.Tendsto Ib (nhds t) (nhds (Ib t)) := by
    have hax : Filter.Tendsto (fun b : ℝ => ((b : ℂ) * Complex.I)) (nhds t) (nhdsWithin ((t : ℂ) * Complex.I) Oψ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((Complex.continuous_ofReal.mul continuous_const).tendsto t))
        (Filter.Eventually.of_forall fun b => hOψax (by simp))
    have hlim := (hBψ.2 _ (hOψax (by simp : (((t : ℂ) * Complex.I)).re = 0))).comp hax
    have hbound : ∀ b : ℝ, ‖Ib b - Ib t‖ ≤ (eLpNorm Lφ 2 μΦ).toReal * (eLpNorm (Lψ b - Lψ t) 2 μΦ).toReal := by
      intro b
      have hi : ∀ b' : ℝ, Integrable (fun x => Lφ x * conj (Lψ b' x)) μΦ := fun b' => hmemφ.integrable_mul (hmemψc b')
      have hsub : Ib b - Ib t = ∫ x, Lφ x * conj ((Lψ b - Lψ t) x) ∂μΦ := by
        simp only [hIb, hμΦ]
        rw [← integral_sub (hi b) (hi t)]
        congr 1; funext x; simp only [Pi.sub_apply, map_sub]; ring
      rw [hsub]
      have h1 : ‖∫ x, Lφ x * conj ((Lψ b - Lψ t) x) ∂μΦ‖ ≤ ∫ x, ‖Lφ x‖ * ‖(Lψ b - Lψ t) x‖ ∂μΦ := by
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        congr 1; funext x; rw [norm_mul, Complex.norm_conj]
      have hmd : MemLp (Lψ b - Lψ t) 2 μΦ := (hmemψ b).sub (hmemψ t)
      have h2 := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μΦ) (p := 2) (q := 2)
        Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall fun x => norm_nonneg (Lφ x)) (Filter.Eventually.of_forall fun x => norm_nonneg ((Lψ b - Lψ t) x))
        (by simpa using hmemφ.norm) (by simpa using hmd.norm)
      refine h1.trans (h2.trans (le_of_eq ?_))
      rw [hmemφ.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
        hmd.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
      norm_num
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hK : 0 < (eLpNorm Lφ 2 μΦ).toReal + 1 := by positivity
    have hev : ∀ᶠ b in nhds t, eLpNorm (Lψ b - Lψ t) 2 μΦ < ENNReal.ofReal (ε / ((eLpNorm Lφ 2 μΦ).toReal + 1)) :=
      hlim (Iio_mem_nhds (by simpa using div_pos hε hK))
    filter_upwards [hev] with b hb
    rw [dist_eq_norm]
    have hfin : eLpNorm (Lψ b - Lψ t) 2 μΦ ≠ ⊤ := ((hmemψ b).sub (hmemψ t)).eLpNorm_ne_top
    have hb' : (eLpNorm (Lψ b - Lψ t) 2 μΦ).toReal < ε / ((eLpNorm Lφ 2 μΦ).toReal + 1) := by
      rw [← ENNReal.toReal_ofReal (div_pos hε hK).le]; exact (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hb
    calc ‖Ib b - Ib t‖ ≤ (eLpNorm Lφ 2 μΦ).toReal * (eLpNorm (Lψ b - Lψ t) 2 μΦ).toReal := hbound b
      _ ≤ ((eLpNorm Lφ 2 μΦ).toReal + 1) * (eLpNorm (Lψ b - Lψ t) 2 μΦ).toReal := by
          gcongr; linarith
      _ < ((eLpNorm Lφ 2 μΦ).toReal + 1) * (ε / ((eLpNorm Lφ 2 μΦ).toReal + 1)) := by gcongr
      _ = ε := by field_simp
  have hlimL : Filter.Tendsto Ib (nhdsWithin t {t}ᶜ) (nhds (Ib t)) := hIlim.mono_left nhdsWithin_le_nhds

  have hlin : HasDerivAt (fun b : ℝ => (((t - b : ℝ) : ℂ) * Complex.I)) (-Complex.I) t := by
    have h1 : HasDerivAt (fun b : ℝ => ((t - b : ℝ) : ℂ)) (-1) t := by
      have := ((hasDerivAt_const t t).sub (hasDerivAt_id t)).ofReal_comp
      simpa using this
    simpa using h1.mul_const Complex.I
  have hexp1 : HasDerivAt (fun b : ℝ => Complex.exp ((R : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I))) (-(R : ℂ) * Complex.I) t := by
    have := (hlin.const_mul (R : ℂ)).cexp
    simp only [sub_self, Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero, one_mul] at this
    convert this using 1 <;> first | rfl | ring
  have hexp2 : HasDerivAt (fun b : ℝ => Complex.exp (-((R : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I)))) ((R : ℂ) * Complex.I) t := by
    have hlin2 : HasDerivAt (fun b : ℝ => -((R : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I))) ((R : ℂ) * Complex.I) t := by
      have := (hlin.const_mul (R : ℂ)).neg
      convert this using 1 <;> first | rfl | ring
    have := hlin2.cexp
    simp only [sub_self, Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero, one_mul] at this
    exact this

  set T : ℝ → ℂ := fun b => P3 b * Complex.exp ((R : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)) / (((t + b : ℝ) : ℂ) * Complex.I)
    - P4 b * Complex.exp (-((R : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I))) / (((t + b : ℝ) : ℂ) * Complex.I) with hT
  have hTc : t ≠ 0 → ContinuousAt T t := by
    intro ht
    have hden : (((t + t : ℝ) : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (show t + t ≠ 0 by intro h; apply ht; linarith)) Complex.I_ne_zero
    simp only [hT]
    have hl : Continuous fun b : ℝ => (((t + b : ℝ) : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).mul continuous_const
    refine ((hP3c.continuousAt.mul (Complex.continuous_exp.comp (continuous_const.mul hl)).continuousAt).div
      hl.continuousAt hden).sub ?_
    exact ((hP4c.continuousAt.mul (Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul hl))).continuousAt).div
      hl.continuousAt hden)
  have hnb : t ≠ 0 → ∀ᶠ b in nhds t, t + b ≠ 0 := by
    intro ht
    filter_upwards [Metric.ball_mem_nhds t (abs_pos.mpr ht)] with b hb
    rw [Metric.mem_ball, Real.dist_eq] at hb
    intro h
    have : b = -t := by linarith
    rw [this] at hb
    have : |(-t) - t| = 2 * |t| := by rw [show (-t) - t = -(2 * t) by ring, abs_neg, abs_mul, abs_two]
    linarith [abs_nonneg t]
  have hne : ∀ᶠ b in nhdsWithin t {t}ᶜ, b ≠ t := eventually_nhdsWithin_of_forall fun b hb => hb
  have e1 : (R : ℂ) * (((t + t : ℝ) : ℂ) * Complex.I) = 2 * Complex.I * (R : ℂ) * (t : ℂ) := by push_cast; ring
  have e2 : ((t + t : ℝ) : ℂ) * Complex.I = 2 * Complex.I * (t : ℂ) := by push_cast; ring
  refine ⟨hint, ?_, ?_, ?_, ?_⟩
  ·
    intro h1 h2 hμν ht
    subst h1
    subst h2

    have hU := AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar L hαm _ _ hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
      Oφ Eφ Nφ ⟨hOφ, hOφc, hOφax, hOφhalf, hEφa, hNφa, hEφjc, hNφjc, hEφE, hNφN⟩
      Oψ Eψ Nψ ⟨hOψ, hOψc, hOψax, hOψhalf, hEψa, hNψa, hEψjc, hNψjc, hEψE, hNψN⟩ t
    have hP2t : P2 t = P1 t := by simp only [hP2, hP1, hvC]; exact hU
    have hMSb : ∀ b : ℝ, t ≠ b → t + b ≠ 0 →
        Ib b = (c : ℂ) *
          ( P1 b * Complex.exp ((R : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I)) / (((t - b : ℝ) : ℂ) * Complex.I)
          - P2 b * Complex.exp (-((R : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I))) / (((t - b : ℝ) : ℂ) * Complex.I)
          + P3 b * Complex.exp ((R : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)) / (((t + b : ℝ) : ℂ) * Complex.I)
          - P4 b * Complex.exp (-((R : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I))) / (((t + b : ℝ) : ℂ) * Complex.I) ) := by
      intro b hb hbb
      have h := ((hMS _ _ _ _ hμ hν hμ' hν' hμF hνF hμ'F hν'F hμk hνk hμ'k hν'k φf hφf hφfK hφff hφfjc hφfhol hφfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
        Oφ Eφ Nφ ⟨hOφ, hOφc, hOφax, hOφhalf, hEφa, hNφa, hEφjc, hNφjc, hEφE, hNφN⟩
        Oψ Eψ Nψ ⟨hOψ, hOψc, hOψax, hOψhalf, hEψa, hNψa, hEψjc, hNψjc, hEψE, hNψN⟩ t b hb R hR).1 rfl rfl hμν hbb).2
      rw [hsum, hdiff] at h
      simp only [hIb, hLφ, hLψ, hP1, hP2, hP3, hP4, hvC]
      exact h

    set N : ℝ → ℂ := fun b => P1 t * Complex.exp ((R : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I)) -
      P2 b * Complex.exp (-((R : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I))) with hN
    have hN0 : N t = 0 := by
      simp only [hN, sub_self, Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero, mul_one, hP2t]
    have hNd : HasDerivAt N (P1 t * (-(R : ℂ) * Complex.I) - (-Complex.I * Q * 1 + P2 t * ((R : ℂ) * Complex.I))) t := by
      simp only [hN]
      refine (hexp1.const_mul (P1 t)).sub ?_
      have := hP2d.mul hexp2
      simp only [sub_self, Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero] at this
      exact this
    have hlimN := AxisAux.tendsto_div_of_hasDerivAt hNd hN0

    have hev : ∀ᶠ b in nhdsWithin t {t}ᶜ, Ib b = (c : ℂ) * (N b / (Complex.I * ((t : ℂ) - (b : ℂ))) + T b) := by
      filter_upwards [hne, (hnb ht).filter_mono nhdsWithin_le_nhds] with b hb hbb
      rw [hMSb b (Ne.symm hb) hbb, hP1const b]
      simp only [hN, hT]
      have hD : (((t - b : ℝ) : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (sub_ne_zero.mpr (Ne.symm hb))) Complex.I_ne_zero
      have hD2 : Complex.I * ((t : ℂ) - (b : ℂ)) ≠ 0 := by
        rw [mul_comm, ← Complex.ofReal_sub]; exact hD
      push_cast
      field_simp
      ring

    have hlimR : Filter.Tendsto (fun b => (c : ℂ) * (N b / (Complex.I * ((t : ℂ) - (b : ℂ))) + T b)) (nhdsWithin t {t}ᶜ)
        (nhds ((c : ℂ) * (-(P1 t * (-(R : ℂ) * Complex.I) - (-Complex.I * Q * 1 + P2 t * ((R : ℂ) * Complex.I))) / Complex.I + T t))) :=
      (hlimN.add ((hTc ht).tendsto.mono_left nhdsWithin_le_nhds)).const_mul _
    have heq := tendsto_nhds_unique hlimL (hlimR.congr' (hev.mono fun b hb => hb.symm))

    have hfinal : Ib t = (c : ℂ) * (P1 t * (2 * (R : ℂ)) - Q
        + P3 t * Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
        - P4 t * Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ))) := by
      rw [heq, hP2t]
      simp only [hT]
      rw [e1, e2]
      congr 1
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      field_simp
      ring_nf
    simp only [hIb, hLφ, hLψ, hP1, hP3, hP4, hQ, hvC] at hfinal
    exact hfinal
  ·
    intro h1 h2 hoff ht
    subst h1
    subst h2
    have hU := AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar L hαm _ _ hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
      Oφ Eφ Nφ ⟨hOφ, hOφc, hOφax, hOφhalf, hEφa, hNφa, hEφjc, hNφjc, hEφE, hNφN⟩
      Oψ Eψ Nψ ⟨hOψ, hOψc, hOψax, hOψhalf, hEψa, hNψa, hEψjc, hNψjc, hEψE, hNψN⟩ t
    have hP2t : P2 t = P1 t := by simp only [hP2, hP1, hvC]; exact hU
    have hMSb : ∀ b : ℝ, t ≠ b →
        Ib b = (c : ℂ) *
          ( P1 b * Complex.exp ((R : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I)) / (((t - b : ℝ) : ℂ) * Complex.I)
          - P2 b * Complex.exp (-((R : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I))) / (((t - b : ℝ) : ℂ) * Complex.I) ) := by
      intro b hb
      have h := ((hMS _ _ _ _ hμ hν hμ' hν' hμF hνF hμ'F hν'F hμk hνk hμ'k hν'k φf hφf hφfK hφff hφfjc hφfhol hφfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
        Oφ Eφ Nφ ⟨hOφ, hOφc, hOφax, hOφhalf, hEφa, hNφa, hEφjc, hNφjc, hEφE, hNφN⟩
        Oψ Eψ Nψ ⟨hOψ, hOψc, hOψax, hOψhalf, hEψa, hNψa, hEψjc, hNψjc, hEψE, hNψN⟩ t b hb R hR).2.1 rfl rfl hoff).2
      rw [hsum] at h
      simp only [hIb, hLφ, hLψ, hP1, hP2, hvC]
      exact h
    set N : ℝ → ℂ := fun b => P1 t * Complex.exp ((R : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I)) -
      P2 b * Complex.exp (-((R : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I))) with hN
    have hN0 : N t = 0 := by
      simp only [hN, sub_self, Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero, mul_one, hP2t]
    have hNd : HasDerivAt N (P1 t * (-(R : ℂ) * Complex.I) - (-Complex.I * Q * 1 + P2 t * ((R : ℂ) * Complex.I))) t := by
      simp only [hN]
      refine (hexp1.const_mul (P1 t)).sub ?_
      have := hP2d.mul hexp2
      simp only [sub_self, Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero] at this
      exact this
    have hlimN := AxisAux.tendsto_div_of_hasDerivAt hNd hN0
    have hev : ∀ᶠ b in nhdsWithin t {t}ᶜ, Ib b = (c : ℂ) * (N b / (Complex.I * ((t : ℂ) - (b : ℂ)))) := by
      filter_upwards [hne] with b hb
      rw [hMSb b (Ne.symm hb), hP1const b]
      simp only [hN]
      have hD : (((t - b : ℝ) : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (sub_ne_zero.mpr (Ne.symm hb))) Complex.I_ne_zero
      have hD2 : Complex.I * ((t : ℂ) - (b : ℂ)) ≠ 0 := by
        rw [mul_comm, ← Complex.ofReal_sub]; exact hD
      push_cast
      field_simp
    have hlimR : Filter.Tendsto (fun b => (c : ℂ) * (N b / (Complex.I * ((t : ℂ) - (b : ℂ))))) (nhdsWithin t {t}ᶜ)
        (nhds ((c : ℂ) * (-(P1 t * (-(R : ℂ) * Complex.I) - (-Complex.I * Q * 1 + P2 t * ((R : ℂ) * Complex.I))) / Complex.I))) :=
      hlimN.const_mul _
    have heq := tendsto_nhds_unique hlimL (hlimR.congr' (hev.mono fun b hb => hb.symm))
    have hfinal : Ib t = (c : ℂ) * (P1 t * (2 * (R : ℂ)) - Q) := by
      rw [heq, hP2t]
      congr 1
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      field_simp
      ring_nf
    simp only [hIb, hLφ, hLψ, hP1, hQ, hvC] at hfinal
    exact hfinal
  ·
    intro h1 h2 hoff ht
    have hMSb : ∀ b : ℝ, t ≠ b → t + b ≠ 0 →
        Ib b = (c : ℂ) *
          ( P3 b * Complex.exp ((R : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)) / (((t + b : ℝ) : ℂ) * Complex.I)
          - P4 b * Complex.exp (-((R : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I))) / (((t + b : ℝ) : ℂ) * Complex.I) ) := by
      intro b hb hbb
      have h := ((hMS _ _ _ _ hμ hν hμ' hν' hμF hνF hμ'F hν'F hμk hνk hμ'k hν'k φf hφf hφfK hφff hφfjc hφfhol hφfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
        Oφ Eφ Nφ ⟨hOφ, hOφc, hOφax, hOφhalf, hEφa, hNφa, hEφjc, hNφjc, hEφE, hNφN⟩
        Oψ Eψ Nψ ⟨hOψ, hOψc, hOψax, hOψhalf, hEψa, hNψa, hEψjc, hNψjc, hEψE, hNψN⟩ t b hb R hR).2.2.1 h1 h2 hoff hbb).2
      rw [hdiff] at h
      simp only [hIb, hLφ, hLψ, hP3, hP4, hvC]
      exact h
    have hev : ∀ᶠ b in nhdsWithin t {t}ᶜ, Ib b = (c : ℂ) * T b := by
      filter_upwards [hne, (hnb ht).filter_mono nhdsWithin_le_nhds] with b hb hbb
      rw [hMSb b (Ne.symm hb) hbb]
    have hlimR : Filter.Tendsto (fun b => (c : ℂ) * T b) (nhdsWithin t {t}ᶜ) (nhds ((c : ℂ) * T t)) :=
      ((hTc ht).tendsto.mono_left nhdsWithin_le_nhds).const_mul _
    have heq := tendsto_nhds_unique hlimL (hlimR.congr' (hev.mono fun b hb => hb.symm))
    have hfinal : Ib t = (c : ℂ) * (P3 t * Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
        - P4 t * Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ))) := by
      rw [heq]
      simp only [hT]
      rw [e1, e2]
    simp only [hIb, hLφ, hLψ, hP3, hP4, hvC] at hfinal
    exact hfinal
  ·
    intro hD1 hD2
    have hMSb : ∀ b : ℝ, t ≠ b → Ib b = 0 := by
      intro b hb
      have h := ((hMS _ _ _ _ hμ hν hμ' hν' hμF hνF hμ'F hν'F hμk hνk hμ'k hν'k φf hφf hφfK hφff hφfjc hφfhol hφfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
        Oφ Eφ Nφ ⟨hOφ, hOφc, hOφax, hOφhalf, hEφa, hNφa, hEφjc, hNφjc, hEφE, hNφN⟩
        Oψ Eψ Nψ ⟨hOψ, hOψc, hOψax, hOψhalf, hEψa, hNψa, hEψjc, hNψjc, hEψE, hNψN⟩ t b hb R hR).2.2.2 hD1 hD2).2
      simp only [hIb, hLφ, hLψ]
      exact h
    have hev : ∀ᶠ b in nhdsWithin t {t}ᶜ, Ib b = 0 := by
      filter_upwards [hne] with b hb
      exact hMSb b (Ne.symm hb)
    have hlimR : Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) (nhdsWithin t {t}ᶜ) (nhds 0) := tendsto_const_nhds
    have heq := tendsto_nhds_unique hlimL (hlimR.congr' (hev.mono fun b hb => hb.symm))
    have hfinal : Ib t = 0 := heq
    simp only [hIb, hLφ, hLψ] at hfinal
    exact hfinal

end S_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_canonicalTruncationDomain_of_flat
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_canonicalTruncationDomain_of_flat (solution)
