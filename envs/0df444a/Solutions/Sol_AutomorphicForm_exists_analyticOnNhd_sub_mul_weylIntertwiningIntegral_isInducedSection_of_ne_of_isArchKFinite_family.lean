-- Prove2me | solution 1 for AutomorphicForm.exists_analyticOnNhd_sub_mul_weylIntertwiningIntegral_isInducedSection_of_ne_of_isArchKFinite_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6d728a57-1889-5dab-98de-512710aa0812

import Theorems.Thm_AutomorphicForm_isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family
import Theorems.Thm_AutomorphicForm_exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Theorems.Thm_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth
import Theorems.Thm_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Theorems.Thm_NumberField_TateGlobal_exists_forall_differentiableOn_eq_sub_mul_partialEulerProduct_localChar_of_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_analyticOnNhd_sub_mul_weylIntertwiningIntegral_isInducedSection_of_ne_of_isArchKFinite_family
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain Filter Topology
open scoped NNReal

noncomputable section

namespace B1Proof

section Generic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem isUnitaryChar_one : IsUnitaryChar R K (1 : (AdeleRing R K)ˣ →* ℂˣ) := by
  intro x; simp

theorem isInducedSection_finset_sum {ι : Type*} (t : Finset ι) {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    (c : ι → ℂ) (f : ι → AdelicGL2 R K → ℂ) (hf : ∀ i ∈ t, IsInducedSection R K χ₁ χ₂ (f i)) :
    IsInducedSection R K χ₁ χ₂ (fun x => ∑ i ∈ t, c i * f i x) := by
  intro b hb g
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [hf i hi b hb g]
  ring

variable [MeasurableSpace (AdeleRing R K)]

theorem weylIntertwiningIntegral_apply_eq_translate (ν : Measure (AdeleRing R K))
    (f : AdelicGL2 R K → ℂ) (k : AdelicGL2 R K) :
    weylIntertwiningIntegral R K ν f k = weylIntertwiningIntegral R K ν (fun x => f (x * k)) 1 := by
  unfold weylIntertwiningIntegral
  congr 1
  ext x
  rw [mul_one]

theorem weylIntertwiningIntegral_finset_sum {ι : Type*} (t : Finset ι) (ν : Measure (AdeleRing R K))
    (c : ι → ℂ) (f : ι → AdelicGL2 R K → ℂ) (g : AdelicGL2 R K)
    (hf : ∀ i ∈ t, Integrable (fun x => f i ((adelicWeyl R K)⁻¹ * unipotentGL2 x * g)) ν) :
    weylIntertwiningIntegral R K ν (fun x => ∑ i ∈ t, c i * f i x) g
      = ∑ i ∈ t, c i * weylIntertwiningIntegral R K ν (f i) g := by
  unfold weylIntertwiningIntegral
  rw [integral_finsetSum t (fun i hi => (hf i hi).const_mul (c i))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact integral_const_mul _ _

end Generic

section Chars

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem isUnitaryChar_mul_inv {μ ν : (AdeleRing R K)ˣ →* ℂˣ} (hμ : IsUnitaryChar R K μ) (hν : IsUnitaryChar R K ν) :
    IsUnitaryChar R K (μ * ν⁻¹) := by
  intro x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hμ x,
    hν x, inv_one, mul_one]

theorem isIdeleClassChar_mul_inv {μ ν : (AdeleRing R K)ˣ →* ℂˣ} (hμ : IsIdeleClassChar R K μ)
    (hν : IsIdeleClassChar R K ν) : IsIdeleClassChar R K (μ * ν⁻¹) := by
  intro u
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ u, hν u, inv_one, mul_one]

theorem mul_inv_ne_one_of_ne {μ ν : (AdeleRing R K)ˣ →* ℂˣ} (hne : μ ≠ ν) : μ * ν⁻¹ ≠ 1 :=
  fun h => hne (mul_inv_eq_one.mp h)

end Chars

end B1Proof

namespace B1Proof

section Hecke

variable (F : Type) [Field F] [NumberField F]

theorem norm_absNorm_cpow_neg (v : HeightOneSpectrum (𝓞 F)) (z : ℂ) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-z.re) := by
  have hpos : 0 < Ideal.absNorm v.asIdeal := by
    refine Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem norm_absNorm_cpow_neg_lt_one (v : HeightOneSpectrum (𝓞 F)) {z : ℂ} (hz : 0 < z.re) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)‖ < 1 := by
  rw [norm_absNorm_cpow_neg]
  have h2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm F v
  have h1 : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

theorem summable_norm_absNorm_cpow_neg (S : Finset (HeightOneSpectrum (𝓞 F))) {z : ℂ} (hz : 1 < z.re) :
    Summable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)‖) := by
  have h := (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt F hz).subtype
    {v : HeightOneSpectrum (𝓞 F) | v ∉ S}
  refine h.congr (fun v => ?_)
  simp only [Function.comp_apply]
  rw [norm_absNorm_cpow_neg]

variable {F}

theorem norm_mul_absNorm_cpow_neg_lt_one {S : Finset (HeightOneSpectrum (𝓞 F))}
    (z : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1)
    (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) {w : ℂ} (hw : 0 < w.re) :
    ‖z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)‖ < 1 := by
  rw [norm_mul]
  calc ‖z v‖ * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)‖
      ≤ 1 * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)‖ :=
        mul_le_mul_of_nonneg_right (hz v) (norm_nonneg _)
    _ < 1 := by rw [one_mul]; exact norm_absNorm_cpow_neg_lt_one F v.1 hw

variable (F)

theorem tprod_one_sub_mul_tprod_inv_eq_one' (S : Finset (HeightOneSpectrum (𝓞 F)))
    (z : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) {w : ℂ} (hw : 1 < w.re)
    (hmul : Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹)) :
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))
      * (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹)
      = 1 := by
  have hmul' : Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))) := by
    have hs : Summable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        ‖-(z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))‖) := by
      refine (summable_norm_absNorm_cpow_neg F S hw).of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_)
      rw [norm_neg, norm_mul]
      calc ‖z v‖ * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)‖
          ≤ 1 * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)‖ :=
            mul_le_mul_of_nonneg_right (hz v) (norm_nonneg _)
        _ = _ := one_mul _
    have := multipliable_one_add_of_summable (f := fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      -(z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))) hs
    simpa only [sub_eq_add_neg] using this
  rw [← hmul'.tprod_mul hmul]
  have : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)) *
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹ = 1 := by
    intro v
    apply mul_inv_cancel₀
    intro h
    have hlt := norm_mul_absNorm_cpow_neg_lt_one z hz v (w := w) (by linarith)
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hlt
    exact lt_irrefl _ hlt
  simp only [this, tprod_one]

theorem exists_heckeRegularisation (S : Finset (HeightOneSpectrum (𝓞 F)))
    (z : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) (s₁ : ℂ) (Qh : ℂ → ℂ)
    (hQd : DifferentiableOn ℂ Qh {w : ℂ | 0 < w.re})
    (hQeq : ∀ w : ℂ, 1 < w.re → Qh w = (w - s₁) * (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) :
    ∃ Q : ℂ → ℂ, DifferentiableOn ℂ Q {s : ℂ | 1 / 4 < s.re} ∧
      ∀ s : ℂ, 1 / 2 < s.re → ∀ M R : ℂ,
        (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))) * M
          = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * R →
        (s - s₁ / 2) * M = Q s * R := by
  classical
  obtain ⟨hE3m, hE3d, hE3ne⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S z hz
  set E₃ : ℂ → ℂ := fun w => ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹ with hE₃

  refine ⟨fun s => (1 / 2 : ℂ) * Qh (2 * s) * (E₃ (2 * s + 1))⁻¹, ?_, ?_⟩
  ·
    have h2s : DifferentiableOn ℂ (fun s : ℂ => Qh (2 * s)) {s : ℂ | 1 / 4 < s.re} := by
      refine hQd.comp ((differentiableOn_const _).mul differentiableOn_id) ?_
      intro s hs
      simp only [Set.mem_setOf_eq] at hs ⊢
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      linarith
    have h3 : DifferentiableOn ℂ (fun s : ℂ => E₃ (2 * s + 1)) {s : ℂ | 1 / 4 < s.re} := by
      refine hE3d.comp (((differentiableOn_const _).mul differentiableOn_id).add (differentiableOn_const _)) ?_
      intro s hs
      simp only [Set.mem_setOf_eq] at hs ⊢
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
        Complex.one_re]
      linarith
    have h3ne : ∀ s ∈ {s : ℂ | 1 / 4 < s.re}, E₃ (2 * s + 1) ≠ 0 := by
      intro s hs
      apply hE3ne
      simp only [Set.mem_setOf_eq] at hs
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
        Complex.one_re]
      linarith
    exact ((differentiableOn_const _).mul h2s).mul (h3.inv h3ne)
  ·
    intro s hs M R hid
    have h2s1 : 1 < (2 * s).re := by
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]; linarith
    have h2s11 : 1 < (2 * s + 1).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
        Complex.one_re]; linarith

    have hP2 := tprod_one_sub_mul_tprod_inv_eq_one' F S z hz h2s1 (hE3m _ h2s1)
    have hP3 := tprod_one_sub_mul_tprod_inv_eq_one' F S z hz h2s11 (hE3m _ h2s11)
    change (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))) * E₃ (2 * s) = 1 at hP2
    change (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * E₃ (2 * s + 1) = 1 at hP3
    have hQ2s : Qh (2 * s) = (2 * s - s₁) * E₃ (2 * s) := by
      rw [hQeq (2 * s) h2s1, inv_eq_of_mul_eq_one_right hP2]

    have hM : M = E₃ (2 * s) * ((∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * R) := by
      have := congrArg (fun w => E₃ (2 * s) * w) hid
      rw [← mul_assoc, mul_comm (E₃ (2 * s)), hP2, one_mul] at this
      exact this
    have hE3inv : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) = (E₃ (2 * s + 1))⁻¹ :=
      eq_inv_of_mul_eq_one_left hP3
    rw [hM, hE3inv]
    show _ = (1 / 2 * Qh (2 * s) * (E₃ (2 * s + 1))⁻¹) * R
    rw [hQ2s]
    ring

end Hecke

end B1Proof

namespace B1Proof

namespace T1Helpers

section B1

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem diagOne_val {A : Type*} [CommRing A] (a : Aˣ) :
    ((diagOne a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(a : A), 0; 0, 1] := by
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem diagOne_inv_val {A : Type*} [CommRing A] (a : Aˣ) :
    (((diagOne a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![((a⁻¹ : Aˣ) : A), 0; 0, 1] := by
  rw [← map_inv, diagOne_val]

theorem centralScalar_val (z : (AdeleRing R K)ˣ) :
    ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = !![(z : AdeleRing R K), 0; 0, (z : AdeleRing R K)] := by
  change Matrix.scalar (Fin 2) (z : AdeleRing R K) = _
  ext i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem diagOne_mem_adelicBorel (y : (AdeleRing R K)ˣ) : (diagOne y : AdelicGL2 R K) ∈ adelicBorel R K := by
  show ((diagOne y : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
  rw [diagOne_val]
  simp

end B1

end T1Helpers

section TorusChi

open NumberField NumberField.AdelicLevel AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

theorem T1U_continuous_diagOne : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (diagOne y : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![(y : AdeleRing (𝓞 F) F), 0; 0, 1] := fun y => T1Helpers.diagOne_val y
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_val
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, (((diagOne y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, 1] := fun y => T1Helpers.diagOne_inv_val y
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((diagOne y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_coe_inv
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const

theorem T1U_continuous_centralScalar :
    Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![(y : AdeleRing (𝓞 F) F), 0; 0, (y : AdeleRing (𝓞 F) F)] := fun y => T1Helpers.centralScalar_val (𝓞 F) F y
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_val
    · exact continuous_const
    · exact continuous_const
    · exact Units.continuous_val
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, (((centralScalar (𝓞 F) F y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)] :=
      fun y => by rw [← map_inv]; exact T1Helpers.centralScalar_val (𝓞 F) F y⁻¹
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((centralScalar (𝓞 F) F y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_coe_inv
    · exact continuous_const
    · exact continuous_const
    · exact Units.continuous_coe_inv

theorem T1U_borelDiagFst_diagOne (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨diagOne y, T1Helpers.diagOne_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = y := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = y
  rw [T1Helpers.diagOne_val]
  simp

theorem T1U_borelDiagSnd_diagOne (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨diagOne y, T1Helpers.diagOne_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = 1
  rw [T1Helpers.diagOne_val]
  simp

theorem T1U_borelDiagFst_centralScalar (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨centralScalar (𝓞 F) F y, centralScalar_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = y := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = y
  rw [T1Helpers.centralScalar_val]
  simp

theorem T1U_borelDiagSnd_centralScalar (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨centralScalar (𝓞 F) F y, centralScalar_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = y := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = y
  rw [T1Helpers.centralScalar_val]
  simp

theorem T1U_continuous_monoidHom_units_of_continuous_val (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (h : Continuous fun y => ((χ y : ℂˣ) : ℂ)) : Continuous χ := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((χ y)⁻¹ : ℂˣ) : ℂ)
  simp_rw [← map_inv]
  exact h.comp continuous_inv

theorem T1U_continuous_chars_of_isInducedSection (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαc : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((α y : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
    (hφjc : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)
    (hne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0) :
    Continuous μ ∧ Continuous ν := by
  obtain ⟨s₀, g₀, h0⟩ := hne
  have hφc : Continuous (φ s₀) := hφjc.comp (continuous_const.prodMk continuous_id)
  have hαC : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((((α y : ℝˣ) : ℝ)) : ℂ) := Complex.continuous_ofReal.comp hαc
  have hα0 : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((((α y : ℝˣ) : ℝ)) : ℂ) ≠ 0 := fun y => Complex.ofReal_ne_zero.mpr (hα y).ne'
  have hcp : ∀ t : ℂ, Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((cpowChar α hα t y : ℂˣ) : ℂ) := by
    intro t
    simp only [cpowChar_apply_val]
    exact hαC.cpow continuous_const fun y => Complex.ofReal_mem_slitPlane.mpr (hα y)
  have hcp0 : ∀ (t : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ), ((cpowChar α hα t y : ℂˣ) : ℂ) ≠ 0 := fun t y => (cpowChar α hα t y).ne_zero

  have hμval : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((μ y : ℂˣ) : ℂ)
      = φ s₀ (diagOne y * g₀) / (((cpowChar α hα (s₀ + 1 / 2) y : ℂˣ) : ℂ) * φ s₀ g₀) := by
    intro y
    have h := hφ s₀ _ (T1Helpers.diagOne_mem_adelicBorel (𝓞 F) F y) g₀
    rw [T1U_borelDiagFst_diagOne, T1U_borelDiagSnd_diagOne, map_one, Units.val_one, mul_one, etaFst_apply,
      Units.val_mul] at h
    rw [h, eq_div_iff (mul_ne_zero (hcp0 _ y) h0)]
    ring
  have hμc' : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((μ y : ℂˣ) : ℂ) := by
    simp_rw [hμval]
    exact (hφc.comp ((T1U_continuous_diagOne F).mul continuous_const)).div ((hcp _).mul continuous_const)
      fun y => mul_ne_zero (hcp0 _ y) h0

  have hμνval : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((ν y : ℂˣ) : ℂ)
      = φ s₀ (centralScalar (𝓞 F) F y * g₀) /
        (((μ y : ℂˣ) : ℂ) * ((cpowChar α hα (s₀ + 1 / 2) y : ℂˣ) : ℂ) * ((cpowChar α hα (-(s₀ + 1 / 2)) y : ℂˣ) : ℂ)
          * φ s₀ g₀) := by
    intro y
    have h := hφ s₀ _ (centralScalar_mem_adelicBorel (𝓞 F) F y) g₀
    rw [T1U_borelDiagFst_centralScalar, T1U_borelDiagSnd_centralScalar, etaFst_apply, etaSnd_apply, Units.val_mul,
      Units.val_mul] at h
    rw [h, eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (μ y).ne_zero (hcp0 _ y)) (hcp0 _ y)) h0)]
    ring
  have hνc' : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((ν y : ℂˣ) : ℂ) := by
    simp_rw [hμνval]
    refine (hφc.comp ((T1U_continuous_centralScalar F).mul continuous_const)).div
      (((hμc'.mul (hcp _)).mul (hcp _)).mul continuous_const) fun y => ?_
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (μ y).ne_zero (hcp0 _ y)) (hcp0 _ y)) h0
  exact ⟨T1U_continuous_monoidHom_units_of_continuous_val F μ hμc',
    T1U_continuous_monoidHom_units_of_continuous_val F ν hνc'⟩

end TorusChi

end B1Proof

namespace B1Proof

section Main

variable (F : Type) [Field F] [NumberField F]

def IsK (k : AdelicGL2 (𝓞 F) F) : Prop :=
  glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
    ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))

theorem isK_mul {k k' : AdelicGL2 (𝓞 F) F} (hk : IsK F k) (hk' : IsK F k') : IsK F (k * k') := by
  refine ⟨?_, fun w => ?_⟩
  · rw [map_mul]; exact (finiteIntegralGL2 (𝓞 F) F).mul_mem hk.1 hk'.1
  · rw [map_mul, map_mul]; exact (hk.2 w).mul (hk'.2 w)

theorem isK_one : IsK F 1 := by
  refine ⟨?_, fun w => ?_⟩
  · rw [map_one]; exact (finiteIntegralGL2 (𝓞 F) F).one_mem
  · rw [map_one, map_one]; exact isRowIsometry_one

theorem eq_of_isInducedSection_of_eqOn_K {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {f f' : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsInducedSection (𝓞 F) F χ₁ χ₂ f) (hf' : IsInducedSection (𝓞 F) F χ₁ χ₂ f')
    (h : ∀ k, IsK F k → f k = f' k) : f = f' := by
  funext g
  obtain ⟨b, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  rw [hf b hb k, hf' b hb k, h k ⟨hk1, hk2⟩]

theorem main :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (_hne : μ ≠ ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := adeleBorel (𝓞 F) F
    ∃ (a : ℝ) (s₀ : ℂ) (Mreg : ℂ → AdelicGL2 (𝓞 F) F → ℂ), a < 1 / 2 ∧ s₀ ≠ 1 / 2 ∧ s₀.re ≤ 1 / 2 ∧
      (∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Mreg s h) {s : ℂ | a < s.re}) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        Mreg s h = (s - s₀) * (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) h) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Mreg p.1 p.2)
        ({s : ℂ | a < s.re} ×ˢ Set.univ) ∧
      (∀ s : ℂ, a < s.re →
        IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s)) (Mreg s)) := by
  intro α hα μ ν hμ hν hμF hνF hne φ hφ hφK hφf hφjc hφhol
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  classical

  by_cases hzero : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g = 0
  · refine ⟨0, 0, fun _ _ => 0, by norm_num, by norm_num, by norm_num [Complex.zero_re], ?_, ?_, ?_, ?_⟩
    · intro h
      exact analyticOnNhd_const
    · intro s h hs
      have hM : weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) h = 0 := by
        unfold weylIntertwiningIntegral
        simp only [hzero, integral_zero]
      rw [hM, mul_zero]
    · exact continuousOn_const
    · intro s _ b hb g
      simp
  push Not at hzero

  have hαr : Continuous (fun y : (AdeleRing (𝓞 F) F)ˣ => ((α y : ℝˣ) : ℝ)) :=
    NumberField.TateGlobal.continuous_ideleNorm F
  obtain ⟨hμc, hνc⟩ := T1U_continuous_chars_of_isInducedSection F α hα hαr μ ν φ hφ hφjc hzero
  have hχc : Continuous (μ * ν⁻¹) := by
    refine T1U_continuous_monoidHom_units_of_continuous_val F (μ * ν⁻¹) ?_
    show Continuous fun y => (((μ * ν⁻¹) y : ℂˣ) : ℂ)
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
    exact (Units.continuous_val.comp hμc).mul (Units.continuous_val.comp hνc.inv)
  obtain ⟨s₁, hs₁re, hs₁ne, hHecke⟩ :=
    NumberField.TateGlobal.exists_forall_differentiableOn_eq_sub_mul_partialEulerProduct_localChar_of_ne_one F
      (μ * ν⁻¹) hχc (isUnitaryChar_mul_inv hμ hν) (isIdeleClassChar_mul_inv hμF hνF) (mul_inv_ne_one_of_ne hne)
  have hs0ne : s₁ / 2 ≠ 1 / 2 := by
    intro h
    apply hs₁ne
    linear_combination 2 * h
  have hs0re : (s₁ / 2).re ≤ 1 / 2 := by
    rw [Complex.div_ofNat_re, hs₁re]
  have hzχ : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ),
      ‖((NumberField.TateGlobal.localChar (μ * ν⁻¹) v x : ℂˣ) : ℂ)‖ ≤ 1 :=
    fun v x => (isUnitaryChar_mul_inv hμ hν _).le

  obtain ⟨n, c, ψ, hc, hψ, hψK, hψf, hψjc, hψhol, hψflat, hφsum⟩ :=
    AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family F hα μ ν φ hφ hφK hφf hφjc hφhol

  have hψc0 : ∀ i, Continuous (ψ i 0) := fun i => (hψjc i).comp (Continuous.prodMk_right 0)
  choose m e a he ha hexp using fun i =>
    AutomorphicForm.exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth F (ψ i 0)
      (hψK i 0) (hψf i 0) (hψc0 i)
  have hind_e : ∀ i j, IsInducedSection (𝓞 F) F (etaFst μ α hα 0) (etaSnd ν α hα 0) (e i j) := by
    intro i j
    obtain ⟨nn, cc, kk, _hkk, heq⟩ := (he i j).1
    rw [heq]
    exact isInducedSection_finset_sum Finset.univ cc (fun l x => ψ i 0 (x * kk l))
      (fun l _ => (hψ i 0).rightTranslate (kk l))
  have hcont_e : ∀ i j, Continuous (e i j) := by
    intro i j
    obtain ⟨nn, cc, kk, _hkk, heq⟩ := (he i j).1
    rw [heq]
    exact continuous_finsetSum _ (fun l _ => continuous_const.mul ((hψc0 i).comp (continuous_mul_const _)))

  choose E hE0 hEind hEK hEf hEjc hEhol hEflat using fun i j =>
    AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection F hα μ ν 0 (e i j)
      (hind_e i j) (he i j).2.1 (he i j).2.2 (hcont_e i j)

  have hexpand : ∀ i (s : ℂ) (k : AdelicGL2 (𝓞 F) F), IsK F k →
      (fun x => ψ i s (x * k)) = fun x => ∑ j, a i j k * E i j s x := by
    intro i s k hk
    refine eq_of_isInducedSection_of_eqOn_K F ((hψ i s).rightTranslate k)
      (isInducedSection_finset_sum Finset.univ (fun j => a i j k) (fun j => E i j s) (fun j _ => hEind i j s)) ?_
    intro k' hk'
    have h1 : ψ i s (k' * k) = ψ i 0 (k' * k) :=
      hψflat i s 0 (k' * k) (isK_mul F hk' hk).1 (isK_mul F hk' hk).2
    show ψ i s (k' * k) = ∑ j, a i j k * E i j s k'
    rw [h1, hexp i k hk.1 hk.2 k']
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hE0 i j, hEflat i j 0 s k' hk'.1 hk'.2]

  have hEu : ∀ i j, ∃ (S : Finset (HeightOneSpectrum (𝓞 F)))
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
      (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
      ∃ (Rf : ℂ → ℂ), DifferentiableOn ℂ Rf {s : ℂ | 0 < s.re} ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (E i j s) 1
        = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Rf s := by
    intro i j
    obtain ⟨S, ϖ, hϖ, Rf, _hRm, hRd, hid⟩ :=
      AutomorphicForm.exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul F hα μ ν
        hμ hν (E i j) (hEind i j) (hEK i j) (hEf i j) (hEjc i j) (hEhol i j) 1
    exact ⟨S, ϖ, hϖ, Rf, hRd, fun s hs => hid s hs⟩
  choose S ϖ hϖ Rf hRd hid using hEu

  choose Qh hQhd hQheq using fun i j => hHecke (S i j) (ϖ i j) (hϖ i j)
  choose Q hQd hQid using fun i j => exists_heckeRegularisation F (S i j)
    (fun v => ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ i j v.1) : ℂˣ) : ℂ)) (fun v => hzχ _ _) s₁
    (Qh i j) (hQhd i j) (hQheq i j)

  set vol : ℂ := (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) with hvol
  let mreg : (i : Fin n) → Fin (m i) → ℂ → ℂ := fun i j s => vol⁻¹ * (Q i j s * Rf i j s)
  have hmreg_d : ∀ i j, DifferentiableOn ℂ (mreg i j) {s : ℂ | 1 / 4 < s.re} := by
    intro i j
    exact (differentiableOn_const _).mul ((hQd i j).mul ((hRd i j).mono (fun s hs => by
      simp only [Set.mem_setOf_eq] at hs ⊢; linarith)))
  have hmreg_id : ∀ i j (s : ℂ), 1 / 2 < s.re →
      (s - s₁ / 2) * vol⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (E i j s) 1 = mreg i j s := by
    intro i j s hs
    have h := hQid i j s hs _ _ (hid i j s hs)
    show (s - s₁ / 2) * vol⁻¹ * _ = vol⁻¹ * (Q i j s * Rf i j s)
    rw [← h]; ring

  let χsw : ℂ → ↥(adelicBorel (𝓞 F) F) → ℂ := fun s b =>
    ((etaFst ν α hα (-s) (borelDiagFst b) : ℂˣ) : ℂ) * ((etaSnd μ α hα (-s) (borelDiagSnd b) : ℂˣ) : ℂ)

  choose bI kI hbI hkI1 hkI2 hdecI using fun g : AdelicGL2 (𝓞 F) F => AutomorphicForm.exists_mem_adelicBorel_mul_eq F g

  let Ksum : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s k => ∑ i, c i s * ∑ j, a i j k * mreg i j s
  let Mreg : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h => χsw s ⟨bI h, hbI h⟩ * Ksum s (kI h)

  have hLINK : ∀ (s : ℂ), 1 / 2 < s.re → ∀ k, IsK F k →
      (s - s₁ / 2) * vol⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k = Ksum s k := by
    intro s hs k hk
    rw [weylIntertwiningIntegral_apply_eq_translate]
    have hφk : (fun x => φ s (x * k)) = fun x => ∑ i, c i s * ∑ j, a i j k * E i j s x := by
      funext x
      rw [hφsum s (x * k)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have := congrFun (hexpand i s k hk) x
      rw [this]
    rw [hφk]

    have hint : ∀ i j, Integrable (fun x : AdeleRing (𝓞 F) F =>
        E i j s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * 1)) (adelicAddHaar (𝓞 F) F) := by
      intro i j
      exact AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν hμ
        hν s hs (E i j s) (hEind i j s) ((hEjc i j).comp (Continuous.prodMk_right s)) 1
    have hint' : ∀ i, Integrable (fun x : AdeleRing (𝓞 F) F =>
        (fun y => ∑ j, a i j k * E i j s y) ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * 1)) (adelicAddHaar (𝓞 F) F) := by
      intro i
      simp only
      exact integrable_finsetSum _ (fun j _ => (hint i j).const_mul _)
    rw [weylIntertwiningIntegral_finset_sum Finset.univ _ (fun i => c i s) (fun i y => ∑ j, a i j k * E i j s y) 1
      (fun i _ => hint' i)]
    simp only [Ksum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [weylIntertwiningIntegral_finset_sum Finset.univ _ (fun j => a i j k) (fun j => E i j s) 1 (fun j _ => hint i j)]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hmreg_id i j s hs]
    ring

  have hχsw_eq : ∀ (s : ℂ) (b : ↥(adelicBorel (𝓞 F) F)), χsw s b =
      (((ν (borelDiagFst b) : ℂˣ) : ℂ) * ((((α (borelDiagFst b) : ℝˣ) : ℝ) : ℂ) ^ (-s + 1 / 2))) *
        (((μ (borelDiagSnd b) : ℂˣ) : ℂ) * ((((α (borelDiagSnd b) : ℝˣ) : ℝ) : ℂ) ^ (-(-s + 1 / 2)))) := by
    intro s b
    simp only [χsw, etaFst_apply, etaSnd_apply, cpowChar_apply_val, Units.val_mul]
  have hχsw_mul : ∀ (s : ℂ) (b b' : ↥(adelicBorel (𝓞 F) F)), χsw s (b * b') = χsw s b * χsw s b' := by
    intro s b b'
    simp only [χsw, map_mul, Units.val_mul]
    ring
  have hχsw_d : ∀ (b : ↥(adelicBorel (𝓞 F) F)), Differentiable ℂ (fun s => χsw s b) := by
    intro b
    have h1 : ∀ (r : ℝ), 0 < r → Differentiable ℂ (fun s : ℂ => ((r : ℂ)) ^ (-s + 1 / 2)) := by
      intro r hr
      exact Differentiable.const_cpow ((differentiable_id.neg).add (differentiable_const _))
        (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))
    have h2 : ∀ (r : ℝ), 0 < r → Differentiable ℂ (fun s : ℂ => ((r : ℂ)) ^ (-(-s + 1 / 2))) := by
      intro r hr
      exact Differentiable.const_cpow (((differentiable_id.neg).add (differentiable_const _)).neg)
        (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))
    have : (fun s => χsw s b) = fun s =>
        (((ν (borelDiagFst b) : ℂˣ) : ℂ) * ((((α (borelDiagFst b) : ℝˣ) : ℝ) : ℂ) ^ (-s + 1 / 2))) *
          (((μ (borelDiagSnd b) : ℂˣ) : ℂ) * ((((α (borelDiagSnd b) : ℝˣ) : ℝ) : ℂ) ^ (-(-s + 1 / 2)))) := by
      funext s; exact hχsw_eq s b
    rw [this]
    exact ((differentiable_const _).mul (h1 _ (hα _))).mul ((differentiable_const _).mul (h2 _ (hα _)))
  have hU : IsOpen {s : ℂ | 1 / 4 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected {s : ℂ | 1 / 4 < s.re} := (convex_halfSpace_re_gt (1 / 4 : ℝ)).isPreconnected
  have hKsum_d : ∀ k, DifferentiableOn ℂ (fun s => Ksum s k) {s : ℂ | 1 / 4 < s.re} := by
    intro k
    refine DifferentiableOn.fun_sum (fun i _ => ((hc i).differentiableOn).mul ?_)
    refine DifferentiableOn.fun_sum (fun j _ => (differentiableOn_const _).mul (hmreg_d i j))
  have hMreg_an : ∀ h, AnalyticOnNhd ℂ (fun s => Mreg s h) {s : ℂ | 1 / 4 < s.re} := by
    intro h
    exact (((hχsw_d _).differentiableOn).mul (hKsum_d _)).analyticOnNhd hU
  have hSWAP : ∀ (s : ℂ) (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) (b * g)
        = χsw s ⟨b, hb⟩ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g := by
    intro s b hb g
    exact AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral F hα μ ν s (φ s) (hφ s) b hb g

  have hMreg_half : ∀ (s : ℂ), 1 / 2 < s.re → ∀ h,
      Mreg s h = (s - s₁ / 2) * vol⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) h := by
    intro s hs h
    show χsw s ⟨bI h, hbI h⟩ * Ksum s (kI h) = _
    rw [← hLINK s hs (kI h) ⟨hkI1 h, hkI2 h⟩]
    conv_rhs => rw [hdecI h]
    rw [hSWAP s (bI h) (hbI h) (kI h)]
    ring

  have hcore : ∀ (s : ℂ), 1 / 4 < s.re → ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (k : AdelicGL2 (𝓞 F) F),
      IsK F k → Mreg s (b * k) = χsw s ⟨b, hb⟩ * Ksum s k := by
    intro s hs b hb k hk
    have hf₁ : AnalyticOnNhd ℂ (fun s => Mreg s (b * k)) {s : ℂ | 1 / 4 < s.re} := hMreg_an _
    have hf₂ : AnalyticOnNhd ℂ (fun s => χsw s ⟨b, hb⟩ * Ksum s k) {s : ℂ | 1 / 4 < s.re} :=
      (((hχsw_d _).differentiableOn).mul (hKsum_d _)).analyticOnNhd hU
    have h1mem : (1 : ℂ) ∈ {s : ℂ | 1 / 4 < s.re} := by simp; norm_num
    have hev : (fun s => Mreg s (b * k)) =ᶠ[𝓝 (1 : ℂ)] (fun s => χsw s ⟨b, hb⟩ * Ksum s k) := by
      have hO : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      have h1 : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by simp; norm_num
      filter_upwards [hO.mem_nhds h1] with s hs'
      rw [hMreg_half s hs' (b * k), hSWAP s b hb k, ← hLINK s hs' k hk]
      ring
    exact hf₁.eqOn_of_preconnected_of_eventuallyEq hf₂ hUpre h1mem hev hs

  have h4 : ∀ s : ℂ, 1 / 4 < s.re →
      IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s)) (Mreg s) := by
    intro s hs b hb g
    have hg : b * g = (b * bI g) * kI g := by rw [mul_assoc, ← hdecI g]
    rw [hg, hcore s hs (b * bI g) ((adelicBorel (𝓞 F) F).mul_mem hb (hbI g)) (kI g) ⟨hkI1 g, hkI2 g⟩]
    have hsplit : (⟨b * bI g, (adelicBorel (𝓞 F) F).mul_mem hb (hbI g)⟩ : ↥(adelicBorel (𝓞 F) F))
        = ⟨b, hb⟩ * ⟨bI g, hbI g⟩ := rfl
    rw [hsplit, hχsw_mul]
    show χsw s ⟨b, hb⟩ * χsw s ⟨bI g, hbI g⟩ * Ksum s (kI g) = χsw s ⟨b, hb⟩ * (χsw s ⟨bI g, hbI g⟩ * Ksum s (kI g))
    ring
  refine ⟨1 / 4, s₁ / 2, Mreg, by norm_num, hs0ne, hs0re, hMreg_an, ?_, ?_, h4⟩
  ·
    intro s h hs
    rw [hMreg_half s hs h]
  ·
    have hαc : Continuous (fun y : (AdeleRing (𝓞 F) F)ˣ => (((α y : ℝˣ) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hαr
    have hslit : ∀ y : (AdeleRing (𝓞 F) F)ˣ, (((α y : ℝˣ) : ℝ) : ℂ) ∈ Complex.slitPlane :=
      fun y => Complex.ofReal_mem_slitPlane.2 (hα y)
    have hχ₁ : ContinuousOn (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((etaFst ν α hα (-p.1) p.2 : ℂˣ) : ℂ))
        ({s : ℂ | 1 / 4 < s.re} ×ˢ Set.univ) := by
      have heq : (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((etaFst ν α hα (-p.1) p.2 : ℂˣ) : ℂ))
          = fun p => ((ν p.2 : ℂˣ) : ℂ) * (((α p.2 : ℝˣ) : ℝ) : ℂ) ^ (-p.1 + 1 / 2) := by
        funext p
        simp only [etaFst_apply, Units.val_mul, cpowChar_apply_val]
      rw [heq]
      refine Continuous.continuousOn ?_
      exact ((Units.continuous_val.comp hνc).comp continuous_snd).mul
        ((hαc.comp continuous_snd).cpow ((continuous_fst.neg).add continuous_const) (fun p => hslit p.2))
    have hχ₂ : ContinuousOn (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((etaSnd μ α hα (-p.1) p.2 : ℂˣ) : ℂ))
        ({s : ℂ | 1 / 4 < s.re} ×ˢ Set.univ) := by
      have heq : (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((etaSnd μ α hα (-p.1) p.2 : ℂˣ) : ℂ))
          = fun p => ((μ p.2 : ℂˣ) : ℂ) * (((α p.2 : ℝˣ) : ℝ) : ℂ) ^ (-(-p.1 + 1 / 2)) := by
        funext p
        simp only [etaSnd_apply, Units.val_mul, cpowChar_apply_val]
      rw [heq]
      refine Continuous.continuousOn ?_
      exact ((Units.continuous_val.comp hμc).comp continuous_snd).mul
        ((hαc.comp continuous_snd).cpow (((continuous_fst.neg).add continuous_const).neg) (fun p => hslit p.2))
    have hKsum_c : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ksum p.1 p.2)
        ({s : ℂ | 1 / 4 < s.re} ×ˢ {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))}) := by
      refine continuousOn_finsetSum _ (fun i _ => ?_)
      refine ContinuousOn.mul (((hc i).continuous).comp_continuousOn continuousOn_fst) ?_
      refine continuousOn_finsetSum _ (fun j _ => ?_)
      refine ContinuousOn.mul ?_ ?_
      · exact (ha i j).comp continuousOn_snd (fun p hp => hp.2)
      · exact ((hmreg_d i j).continuousOn).comp continuousOn_fst (fun p hp => hp.1)
    have hfK : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Mreg p.1 p.2)
        ({s : ℂ | 1 / 4 < s.re} ×ˢ {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))}) := by
      refine hKsum_c.congr (fun p hp => ?_)
      have h1 : Mreg p.1 p.2 = Mreg p.1 (1 * p.2) := by rw [one_mul]
      rw [h1, hcore p.1 hp.1 1 (adelicBorel (𝓞 F) F).one_mem p.2 hp.2]
      have hone : χsw p.1 ⟨1, (adelicBorel (𝓞 F) F).one_mem⟩ = 1 := by
        have : (⟨1, (adelicBorel (𝓞 F) F).one_mem⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := rfl
        rw [this]
        simp only [χsw, map_one, Units.val_one, one_mul]
      rw [hone, one_mul]
    exact AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact F
      {s : ℂ | 1 / 4 < s.re} hU (fun s => etaFst ν α hα (-s)) (fun s => etaSnd μ α hα (-s)) hχ₁ hχ₂ Mreg h4 hfK

end Main

end B1Proof

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (_hne : μ ≠ ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := adeleBorel (𝓞 F) F
    ∃ (a : ℝ) (s₀ : ℂ) (Mreg : ℂ → AdelicGL2 (𝓞 F) F → ℂ), a < 1 / 2 ∧ s₀ ≠ 1 / 2 ∧ s₀.re ≤ 1 / 2 ∧
      (∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Mreg s h) {s : ℂ | a < s.re}) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        Mreg s h = (s - s₀) * (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) h) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Mreg p.1 p.2)
        ({s : ℂ | a < s.re} ×ˢ Set.univ) ∧
      (∀ s : ℂ, a < s.re →
        IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s)) (Mreg s)) :=
  B1Proof.main F

end
end S_AutomorphicForm_exists_analyticOnNhd_sub_mul_weylIntertwiningIntegral_isInducedSection_of_ne_of_isArchKFinite_family
end P2MW
export P2MW.S_AutomorphicForm_exists_analyticOnNhd_sub_mul_weylIntertwiningIntegral_isInducedSection_of_ne_of_isArchKFinite_family (solution)
