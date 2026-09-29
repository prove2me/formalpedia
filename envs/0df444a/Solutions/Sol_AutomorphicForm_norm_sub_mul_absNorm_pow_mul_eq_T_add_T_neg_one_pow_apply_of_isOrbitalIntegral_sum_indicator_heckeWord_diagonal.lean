-- Prove2me | solution 1 for AutomorphicForm.norm_sub_mul_absNorm_pow_mul_eq_T_add_T_neg_one_pow_apply_of_isOrbitalIntegral_sum_indicator_heckeWord_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3d8371cc-2b53-5a7b-8b6f-b9df5b5248f7

import Mathlib
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm
import Theorems.Thm_LocalGL2_sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow
import Theorems.Thm_LocalGL2_mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular
import Theorems.Thm_AutomorphicForm_eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
import Theorems.Thm_HeckeTreeWalk_cast_walkCount_add_sum_mul_pow_sub_pow_eq_choose_mul_pow
import Theorems.Thm_LaurentPolynomial_T_one_add_T_neg_one_pow_apply_eq_sum_ite_choose
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_norm_sub_mul_absNorm_pow_mul_eq_T_add_T_neg_one_pow_apply_of_isOrbitalIntegral_sum_indicator_heckeWord_diagonal
p2m_attr_erase "instance" "NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk"
p2m_attr_erase "simp" "FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open MeasureTheory NumberField IsDedekindDomain
open scoped Pointwise

noncomputable section

namespace P2mSatake

open AutomorphicForm LocalGL2 HeckePair

section Generic

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

abbrev sc (K : Type*) [Field K] : Kˣ →* GL (Fin 2) K :=
  Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom

theorem coe_sc (t : Kˣ) :
    ((sc K t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (t : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Units.coe_map]
  show Matrix.scalar (Fin 2) (t : K) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem central_of_coe_eq_smul {z : GL (Fin 2) K} {a : K}
    (hz : (z : Matrix (Fin 2) (Fin 2) K) = a • (1 : Matrix (Fin 2) (Fin 2) K)) (g : GL (Fin 2) K) :
    Commute z g := by
  show z * g = g * z
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

theorem coe_diagPi_mul_localRepInf :
    ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Units.val_mul, coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem commute_diagPi_localRepInf : Commute (diagPi ϖ hϖ0) (localRepInf ϖ hϖ0 : GL (Fin 2) K) := by
  show diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 = localRepInf ϖ hϖ0 * diagPi ϖ hϖ0
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, coe_diagPi, coe_localRepInf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_diagPi_mul_localRepInf_of_coe {z : GL (Fin 2) K}
    (hz : (z : Matrix (Fin 2) (Fin 2) K) = algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K)) :
    z = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 :=
  Units.ext (hz.trans (coe_diagPi_mul_localRepInf ϖ hϖ0).symm)

theorem sc_mk0_eq_of_coe {z : GL (Fin 2) K}
    (hz : (z : Matrix (Fin 2) (Fin 2) K) = algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K)) :
    sc K (Units.mk0 (algebraMap R K ϖ) hϖ0) = z :=
  Units.ext (by rw [coe_sc, hz]; rfl)

theorem sc_mem_integralSubgroup_of_eq {e : Rˣ} {t : Kˣ} (he : algebraMap R K (e : R) = (t : K)) :
    sc K t ∈ integralSubgroup R K := by
  refine ⟨Units.map (Matrix.scalar (Fin 2) : R →+* Matrix (Fin 2) (Fin 2) R).toMonoidHom e, ?_⟩
  apply Units.ext
  rw [coe_sc]
  show (algebraMap R K).mapMatrix (Matrix.scalar (Fin 2) (e : R)) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, he]

theorem mul_zpow_mul_mem_doubleCoset {G : Type*} [Group G] (U : Subgroup G) {P Q c e x : G}
    (hc : ∀ g : G, Commute c g) (hPQ : Commute P Q) (hcPQ : c = P * Q) (he : e ∈ U)
    (s a b : ℤ) (hx : x ∈ doubleCoset U (P ^ a * Q ^ b)) :
    e * c ^ s * x ∈ doubleCoset U (P ^ (s + a) * Q ^ (s + b)) := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := mem_doubleCoset_iff.mp hx
  refine mem_doubleCoset_iff.mpr ⟨e * u₁, mul_mem he hu₁, u₂, hu₂, ?_⟩
  have h1 : c ^ s * u₁ = u₁ * c ^ s := ((hc u₁).zpow_left s).eq
  have h2 : P ^ (s + a) * Q ^ (s + b) = c ^ s * (P ^ a * Q ^ b) := by
    have h3 : P ^ a * Q ^ s = Q ^ s * P ^ a := (hPQ.zpow_zpow a s).eq
    rw [hcPQ, hPQ.mul_zpow, zpow_add, zpow_add]
    calc P ^ s * P ^ a * (Q ^ s * Q ^ b) = P ^ s * (P ^ a * Q ^ s) * Q ^ b := by simp only [mul_assoc]
      _ = P ^ s * Q ^ s * (P ^ a * Q ^ b) := by rw [h3]; simp only [mul_assoc]
  calc e * u₁ * (P ^ (s + a) * Q ^ (s + b)) * u₂
      = e * (u₁ * c ^ s) * (P ^ a * Q ^ b) * u₂ := by rw [h2]; simp only [mul_assoc]
    _ = e * c ^ s * (u₁ * (P ^ a * Q ^ b) * u₂) := by rw [← h1]; simp only [mul_assoc]

end Generic

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "M2" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

theorem mem_integers_iff_norm (y : Kv) : y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem coe_integers_eq_closedBall :
    (v.adicCompletionIntegers K : Set Kv) = Metric.closedBall (0 : Kv) 1 := by
  ext y
  rw [SetLike.mem_coe, mem_integers_iff_norm, Metric.mem_closedBall, dist_zero_right]

theorem norm_coe_integer_le_one (x : v.adicCompletionIntegers K) : ‖(x : Kv)‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 x.2

theorem uniformiser_ne_zero {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) : (ϖ : Kv) ≠ 0 := by
  intro h
  apply hϖ.ne_zero
  exact_mod_cast h

theorem exists_valued_eq_exp_and_norm_eq {x : Kv} (hx : x ≠ 0) :
    ∃ j : ℤ, Valued.v x = WithZero.exp j ∧ ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ j := by
  have hvx : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v : Valuation Kv (WithZero (Multiplicative ℤ)))).2 hx
  refine ⟨WithZero.log (Valued.v x), (WithZero.exp_log hvx).symm, ?_⟩
  rw [NumberField.FinitePlace.norm_def v x]
  conv_lhs => rw [← WithZero.exp_log hvx]
  rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  congr 1

theorem valued_uniformiser {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : Kv) = WithZero.exp (-1 : ℤ) := by

  obtain ⟨p, hp⟩ := HeightOneSpectrum.intValuation_exists_uniformizer v
  have hpv : Valued.v ((p : 𝓞 K) : Kv) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap, hp]

  set p' : v.adicCompletionIntegers K := algebraMap (𝓞 K) (v.adicCompletionIntegers K) p with hp'
  have hp'v : Valued.v (p' : Kv) = WithZero.exp (-1 : ℤ) := hpv
  have hp'max : p' ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v, hp'v, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    norm_num
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hp'max
  obtain ⟨a, ha⟩ := hp'max
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v (ϖ : Kv) := by
    rw [← hp'v, ← ha]
    push_cast
    rw [map_mul]
    calc Valued.v (a : Kv) * Valued.v (ϖ : Kv) ≤ 1 * Valued.v (ϖ : Kv) :=
          mul_le_mul_of_nonneg_right a.2 zero_le'
      _ = Valued.v (ϖ : Kv) := one_mul _

  have hlt : Valued.v (ϖ : Kv) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have hne : Valued.v (ϖ : Kv) ≠ 0 := (Valuation.ne_zero_iff _).2 (uniformiser_ne_zero K v hϖ)
  refine le_antisymm ?_ hle
  rw [← WithZero.log_le_iff_le_exp hne]
  have h0 : WithZero.log (Valued.v (ϖ : Kv)) < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hne, WithZero.exp_zero]; exact hlt
  omega

theorem norm_uniformiser {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    ‖(ϖ : Kv)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def v, valued_uniformiser K v hϖ,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  rw [← zpow_neg_one]
  congr 1

private theorem _root_.P2mSatake.one_lt_absNorm : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

p2m_export "P2mSatake" "one_lt_absNorm"
theorem norm_uniformiser_pos {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) : 0 < ‖(ϖ : Kv)‖ :=
  norm_pos_iff.2 (uniformiser_ne_zero K v hϖ)

theorem norm_uniformiser_lt_one {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) : ‖(ϖ : Kv)‖ < 1 := by
  rw [norm_uniformiser K v hϖ]
  exact inv_lt_one_of_one_lt₀ (one_lt_absNorm K v)

theorem exists_norm_eq_zpow {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {c : Kv} (hc : c ≠ 0) :
    ∃ k : ℤ, ‖c‖ = ‖(ϖ : Kv)‖ ^ k := by
  obtain ⟨j, -, hj⟩ := exists_valued_eq_exp_and_norm_eq K v hc
  refine ⟨-j, ?_⟩
  rw [hj, norm_uniformiser K v hϖ, inv_zpow', neg_neg]

theorem norm_le_zpow_succ_of_lt {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {x : Kv} {n : ℤ}
    (hx : ‖x‖ < ‖(ϖ : Kv)‖ ^ n) : ‖x‖ ≤ ‖(ϖ : Kv)‖ ^ (n + 1) := by
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero]; exact zpow_nonneg (norm_nonneg _) _
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow K v hϖ hx0
  rw [hk] at hx ⊢
  have h0 := norm_uniformiser_pos K v hϖ
  have h1 := norm_uniformiser_lt_one K v hϖ
  have hnk : n < k := (zpow_lt_zpow_iff_right_of_lt_one₀ h0 h1).1 hx
  exact zpow_le_zpow_right_of_le_one₀ h0 h1.le (by omega)

theorem natCard_quotient_span_uniformiser {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) = Ideal.absNorm v.asIdeal := by
  classical

  have e1 : (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ≃
      IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq).symm.toEquiv

  set f : 𝓞 K →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    (IsLocalRing.residue (v.adicCompletionIntegers K)).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))
    with hf
  have hfs : Function.Surjective f := NumberField.AdelicHaar.residue_algebraMap_surjective (𝓞 K) K v
  have hker : RingHom.ker f = v.asIdeal := by
    refine (Ideal.IsMaximal.eq_of_le v.isMaximal (RingHom.ker_ne_top f) fun a ha => ?_).symm
    rw [RingHom.mem_ker]
    exact NumberField.AdelicHaar.residue_algebraMap_eq_zero_of_mem (𝓞 K) K v ha
  have e2 : (𝓞 K ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hfs)
  rw [Nat.card_congr e1, ← Nat.card_congr e2.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]

section Balls

def ball (ϖ : v.adicCompletionIntegers K) (n : ℤ) : Set Kv := {u | ‖u‖ ≤ ‖(ϖ : Kv)‖ ^ n}

theorem ball_eq_closedBall (ϖ : v.adicCompletionIntegers K) (n : ℤ) :
    ball K v ϖ n = Metric.closedBall (0 : Kv) (‖(ϖ : Kv)‖ ^ n) := by
  ext u; simp [ball, Metric.mem_closedBall, dist_zero_right]

theorem ball_zero (ϖ : v.adicCompletionIntegers K) : ball K v ϖ 0 = (v.adicCompletionIntegers K : Set Kv) := by
  rw [ball_eq_closedBall, zpow_zero, coe_integers_eq_closedBall]

theorem measurableSet_ball [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] (ϖ : v.adicCompletionIntegers K) (n : ℤ) : MeasurableSet (ball K v ϖ n) := by
  rw [ball_eq_closedBall]; exact measurableSet_closedBall

theorem measure_ball_lt_top [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ϖ : v.adicCompletionIntegers K) (n : ℤ) (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ν (ball K v ϖ n) < ⊤ := by
  rw [ball_eq_closedBall]; exact (isCompact_closedBall _ _).measure_lt_top

theorem mem_ball_iff {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (n : ℤ) (u : Kv) :
    u ∈ ball K v ϖ n ↔ ∃ w : Kv, ‖w‖ ≤ 1 ∧ u = (ϖ : Kv) ^ n * w := by
  have h0 := uniformiser_ne_zero K v hϖ
  have hπn : (ϖ : Kv) ^ n ≠ 0 := zpow_ne_zero n h0
  constructor
  · intro hu
    refine ⟨((ϖ : Kv) ^ n)⁻¹ * u, ?_, by rw [← mul_assoc, mul_inv_cancel₀ hπn, one_mul]⟩
    rw [norm_mul, norm_inv, norm_zpow, ← div_eq_inv_mul, div_le_one (zpow_pos (norm_pos_iff.2 h0) n)]
    exact hu
  · rintro ⟨w, hw, rfl⟩
    show ‖(ϖ : Kv) ^ n * w‖ ≤ ‖(ϖ : Kv)‖ ^ n
    rw [norm_mul, norm_zpow]
    exact mul_le_of_le_one_right (zpow_nonneg (norm_nonneg _) n) hw

theorem measure_ball_eq_card_mul_succ [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (n : ℤ)
    (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ν (ball K v ϖ n) = (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ENNReal) * ν (ball K v ϖ (n + 1)) := by
  classical
  have hπ0 : (ϖ : Kv) ≠ 0 := uniformiser_ne_zero K v hϖ
  have hπ1 : ‖(ϖ : Kv)‖ < 1 := norm_uniformiser_lt_one K v hϖ
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_pos_iff.2 hπ0
  set π : Kv := (ϖ : Kv) with hπ
  haveI : Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) := by
    haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := inferInstance
    exact Finite.of_equiv (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
      (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq).toEquiv
  letI : Fintype (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span ({ϖ} : Set (v.adicCompletionIntegers K)))) :=
    Ideal.Quotient.mk_surjective
  set s : v.adicCompletionIntegers K ⧸ Ideal.span {ϖ} → v.adicCompletionIntegers K := Function.surjInv hsurj
    with hs
  have hs_mk : ∀ r, Ideal.Quotient.mk (Ideal.span {ϖ}) (s r) = r := fun r => Function.surjInv_eq hsurj r

  set piece : v.adicCompletionIntegers K ⧸ Ideal.span {ϖ} → Set Kv := fun r =>
    (fun u => -(π ^ n * (s r : Kv)) + u) ⁻¹' ball K v ϖ (n + 1) with hpiece
  have hmem_piece : ∀ r u, u ∈ piece r ↔ ‖u - π ^ n * (s r : Kv)‖ ≤ ‖π‖ ^ (n + 1) := by
    intro r u
    simp only [hpiece, Set.mem_preimage, ball, Set.mem_setOf_eq]
    rw [neg_add_eq_sub]

  have hcong : ∀ a b : v.adicCompletionIntegers K,
      Ideal.Quotient.mk (Ideal.span {ϖ}) a = Ideal.Quotient.mk (Ideal.span {ϖ}) b ↔ ‖(a : Kv) - b‖ ≤ ‖π‖ := by
    intro a b
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩
      have hc' := congrArg (fun x : v.adicCompletionIntegers K => (x : Kv)) hc
      beta_reduce at hc'
      push_cast at hc'
      rw [← hc', norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_coe_integer_le_one K v c)
    · intro hab
      have hint : ‖π⁻¹ * ((a : Kv) - b)‖ ≤ 1 := by
        rw [norm_mul, norm_inv, ← div_eq_inv_mul, div_le_one hπpos]; exact hab
      refine ⟨⟨_, (mem_integers_iff_norm K v _).2 hint⟩, ?_⟩
      apply Subtype.ext
      push_cast
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ0, one_mul]

  have hcover : (⋃ r, piece r) = ball K v ϖ n := by
    ext u
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨r, hr⟩
      rw [hmem_piece] at hr
      show ‖u‖ ≤ ‖π‖ ^ n
      have hsplit : u = (u - π ^ n * (s r : Kv)) + π ^ n * (s r : Kv) := by ring
      rw [hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr.trans ?_) ?_)
      · exact zpow_le_zpow_right_of_le_one₀ hπpos hπ1.le (by omega)
      · rw [norm_mul, norm_zpow]
        exact mul_le_of_le_one_right (zpow_nonneg (norm_nonneg _) n) (norm_coe_integer_le_one K v _)
    · intro hu
      obtain ⟨w, hw1, rfl⟩ := (mem_ball_iff K v hϖ n _).1 hu
      set w' : v.adicCompletionIntegers K := ⟨w, (mem_integers_iff_norm K v _).2 hw1⟩ with hw'
      refine ⟨Ideal.Quotient.mk (Ideal.span {ϖ}) w', ?_⟩
      rw [hmem_piece, ← mul_sub, norm_mul, norm_zpow, zpow_add_one₀ hπpos.ne']
      refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg (norm_nonneg _) n)
      have : (w : Kv) = (w' : Kv) := rfl
      rw [this]
      exact (hcong _ _).1 (hs_mk _).symm

  have hdisj : Pairwise (Function.onFun Disjoint piece) := by
    intro r r' hrr'
    rw [Function.onFun, Set.disjoint_left]
    intro u hur hur'
    rw [hmem_piece] at hur hur'
    apply hrr'
    have hd : ‖π ^ n * ((s r' : Kv) - s r)‖ ≤ ‖π‖ ^ (n + 1) := by
      have : π ^ n * ((s r' : Kv) - s r) = (u - π ^ n * (s r : Kv)) + -(u - π ^ n * (s r' : Kv)) := by ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hur ?_)
      rw [norm_neg]; exact hur'
    rw [norm_mul, norm_zpow, zpow_add_one₀ hπpos.ne'] at hd
    have hd' : ‖(s r' : Kv) - s r‖ ≤ ‖π‖ := le_of_mul_le_mul_left hd (zpow_pos hπpos n)
    rw [← hs_mk r, ← hs_mk r', eq_comm]
    exact (hcong _ _).2 hd'
  have hmeas : ∀ r, MeasurableSet (piece r) := fun r =>
    (measurable_const_add _) (measurableSet_ball K v ϖ (n + 1))
  have hμ : ∀ r, ν (piece r) = ν (ball K v ϖ (n + 1)) := fun r => measure_preimage_add ν _ _
  rw [← hcover, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem measureReal_ball [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (n : ℤ)
    (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ν.real (ball K v ϖ n) = ‖(ϖ : Kv)‖ ^ n * ν.real (ball K v ϖ 0) := by
  have hq : (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℝ) = ‖(ϖ : Kv)‖⁻¹ := by
    rw [natCard_quotient_span_uniformiser K v hϖ, norm_uniformiser K v hϖ, inv_inv]
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_uniformiser_pos K v hϖ

  have hstep : ∀ m : ℤ, ν.real (ball K v ϖ (m + 1)) = ‖(ϖ : Kv)‖ * ν.real (ball K v ϖ m) := by
    intro m
    have h : ν.real (ball K v ϖ m) = ‖(ϖ : Kv)‖⁻¹ * ν.real (ball K v ϖ (m + 1)) := by
      rw [measureReal_def, measure_ball_eq_card_mul_succ K v hϖ m ν, ENNReal.toReal_mul, ENNReal.toReal_natCast, hq,
        measureReal_def]
    rw [h, ← mul_assoc, mul_inv_cancel₀ hπpos.ne', one_mul]

  induction n using Int.induction_on with
  | zero => simp
  | succ m ih =>
    rw [hstep, ih, ← mul_assoc, zpow_add_one₀ hπpos.ne', mul_comm (‖(ϖ : Kv)‖ ^ (m : ℤ))]
  | pred m ih =>
    have h := hstep (-(m : ℤ) - 1)
    rw [show -(m : ℤ) - 1 + 1 = -(m : ℤ) by ring, ih] at h

    have h' : ν.real (ball K v ϖ (-(m : ℤ) - 1)) = ‖(ϖ : Kv)‖⁻¹ * (‖(ϖ : Kv)‖ ^ (-(m : ℤ)) * ν.real (ball K v ϖ 0)) := by
      rw [h, ← mul_assoc, inv_mul_cancel₀ hπpos.ne', one_mul]
    rw [h', ← mul_assoc]
    congr 1
    rw [show -(m : ℤ) - 1 = -((m : ℤ) + 1) by ring, zpow_neg, zpow_neg, zpow_add_one₀ hπpos.ne', mul_inv,
      mul_comm]

end Balls

section Scaled

theorem setOf_norm_mul_le_eq_ball {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {c : Kv} {k : ℤ}
    (hck : ‖c‖ = ‖(ϖ : Kv)‖ ^ k) (n : ℤ) :
    {u : Kv | ‖c * u‖ ≤ ‖(ϖ : Kv)‖ ^ n} = ball K v ϖ (n - k) := by
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_uniformiser_pos K v hϖ
  ext u
  simp only [Set.mem_setOf_eq, ball, norm_mul, hck]
  rw [zpow_sub₀ hπpos.ne', le_div_iff₀' (zpow_pos hπpos k)]

theorem setOf_norm_mul_eq_eq_diff {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {c : Kv} {k : ℤ}
    (hck : ‖c‖ = ‖(ϖ : Kv)‖ ^ k) (n : ℤ) :
    {u : Kv | ‖c * u‖ = ‖(ϖ : Kv)‖ ^ n} = ball K v ϖ (n - k) \ ball K v ϖ (n + 1 - k) := by
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_uniformiser_pos K v hϖ
  have hπ1 : ‖(ϖ : Kv)‖ < 1 := norm_uniformiser_lt_one K v hϖ
  rw [← setOf_norm_mul_le_eq_ball K v hϖ hck n, ← setOf_norm_mul_le_eq_ball K v hϖ hck (n + 1)]
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_diff, not_le]
  constructor
  · intro h
    refine ⟨h.le, ?_⟩
    rw [h]
    exact zpow_lt_zpow_right_of_lt_one₀ hπpos hπ1 (lt_add_one n)
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (norm_le_zpow_succ_of_lt K v hϖ hlt) (not_le.2 h2)

theorem norm_mul_measureReal_setOf_norm_mul_le [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ)
    {c : Kv} (hc : c ≠ 0) (n : ℤ) (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ‖c‖ * ν.real {u : Kv | ‖c * u‖ ≤ ‖(ϖ : Kv)‖ ^ n} =
      ‖(ϖ : Kv)‖ ^ n * ν.real (v.adicCompletionIntegers K : Set Kv) := by
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_uniformiser_pos K v hϖ
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow K v hϖ hc
  rw [setOf_norm_mul_le_eq_ball K v hϖ hk, measureReal_ball K v hϖ, hk, ← ball_zero K v ϖ, ← mul_assoc]
  congr 1
  rw [zpow_sub₀ hπpos.ne']
  field_simp

theorem norm_mul_measureReal_setOf_norm_mul_eq [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ)
    {c : Kv} (hc : c ≠ 0) (n : ℤ) (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ‖c‖ * ν.real {u : Kv | ‖c * u‖ = ‖(ϖ : Kv)‖ ^ n} =
      ‖(ϖ : Kv)‖ ^ n * (1 - ‖(ϖ : Kv)‖) * ν.real (v.adicCompletionIntegers K : Set Kv) := by
  have hπpos : 0 < ‖(ϖ : Kv)‖ := norm_uniformiser_pos K v hϖ
  have hπ1 : ‖(ϖ : Kv)‖ < 1 := norm_uniformiser_lt_one K v hϖ
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow K v hϖ hc
  have hsub : ball K v ϖ (n + 1 - k) ⊆ ball K v ϖ (n - k) := fun u hu =>
    le_trans (α := ℝ) hu (zpow_le_zpow_right_of_le_one₀ hπpos hπ1.le (by omega))
  rw [setOf_norm_mul_eq_eq_diff K v hϖ hk, measureReal_diff hsub (measurableSet_ball K v ϖ _)
    (measure_ball_lt_top K v ϖ _ ν).ne, measureReal_ball K v hϖ (n - k), measureReal_ball K v hϖ (n + 1 - k), hk,
    ← ball_zero K v ϖ]
  rw [zpow_sub₀ hπpos.ne', zpow_sub₀ hπpos.ne', zpow_add_one₀ hπpos.ne']
  field_simp

end Scaled

theorem det_ne_zero (g : GL (Fin 2) (v.adicCompletion K)) :
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 :=
  (Matrix.isUnits_det_units g).ne_zero

theorem norm_entry_le_one_of_mem {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).1 i j)

theorem norm_inv_entry_le_one_of_mem {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).2 i j)

theorem norm_det_le_one {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} (hM : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (hM 0 0) (norm_nonneg _) (hM 1 1)
  · rw [norm_neg, norm_mul]; exact mul_le_one₀ (hM 0 1) (norm_nonneg _) (hM 1 0)

theorem norm_det_eq_one_of_mem {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v) :
    ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 := by
  have h1 : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ≤ 1 :=
    norm_det_le_one K v (norm_entry_le_one_of_mem K v hg)
  have h2 : ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ≤ 1 :=
    norm_det_le_one K v (norm_inv_entry_le_one_of_mem K v hg)
  have hprod : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det *
      ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hn : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ *
      ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  by_contra hne
  have hlt : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ < 1 := lt_of_le_of_ne h1 hne
  have : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ *
      ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt h2
  exact this.ne hn

theorem mem_localIntegralSet_of_norm {g : GL (Fin 2) (v.adicCompletion K)}
    (h1 : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1)
    (h2 : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1) : g ∈ localIntegralSet K v := by
  refine (mem_localIntegralSet K v).2 ⟨fun i j => (mem_integers_iff_norm K v _).2 (h1 i j), fun i j => ?_⟩
  rw [mem_integers_iff_norm, Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv',
    Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, h2, inv_one, one_mul]
  fin_cases i <;> fin_cases j
  · exact h1 1 1
  · simpa using h1 0 1
  · simpa using h1 1 0
  · exact h1 0 0

theorem mem_localIntegralSet_iff_norm (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ localIntegralSet K v ↔ (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1) ∧
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 :=
  ⟨fun hg => ⟨norm_entry_le_one_of_mem K v hg, norm_det_eq_one_of_mem K v hg⟩,
    fun h => mem_localIntegralSet_of_norm K v h.1 h.2⟩

theorem norm_mul_entry_le_one {M N : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} (hM : ∀ i j, ‖M i j‖ ≤ 1)
    (hN : ∀ i j, ‖N i j‖ ≤ 1) (i j : Fin 2) : ‖(M * N) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (hM i 0) (norm_nonneg _) (hN 0 j)
  · rw [norm_mul]; exact mul_le_one₀ (hM i 1) (norm_nonneg _) (hN 1 j)

theorem mul_mem_localIntegralSet {g h : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v)
    (hh : h ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet_iff_norm] at hg hh ⊢
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Units.val_mul]; exact norm_mul_entry_le_one K v hg.1 hh.1 i j
  · rw [Units.val_mul, Matrix.det_mul, norm_mul, hg.2, hh.2, one_mul]

theorem inv_mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v) :
    g⁻¹ ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem mul_mem_localIntegralSet_iff_left {g h : GL (Fin 2) (v.adicCompletion K)} (hh : h ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ g ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hg => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v hgh (inv_mem_localIntegralSet K v hh)
  rwa [mul_inv_cancel_right] at this

theorem mul_mem_localIntegralSet_iff_right {g h : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ h ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hh => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v (inv_mem_localIntegralSet K v hg) hgh
  rwa [inv_mul_cancel_left] at this

theorem conj_mem_localIntegralSet_iff {k g : GL (Fin 2) (v.adicCompletion K)} (hk : k ∈ localIntegralSet K v) :
    k⁻¹ * g * k ∈ localIntegralSet K v ↔ g ∈ localIntegralSet K v := by
  rw [mul_mem_localIntegralSet_iff_left K v hk,
    mul_mem_localIntegralSet_iff_right K v (inv_mem_localIntegralSet K v hk)]

theorem unipotentGL2_mem_iff (t : v.adicCompletion K) : unipotentGL2 t ∈ localIntegralSet K v ↔ ‖t‖ ≤ 1 := by
  rw [mem_localIntegralSet_iff_norm, unipotentGL2_coe, Matrix.det_fin_two_of]
  constructor
  · intro h; simpa using h.1 0 1
  · intro h
    refine ⟨fun i j => ?_, by simp⟩
    fin_cases i <;> fin_cases j <;> simp [h]

private theorem _root_.P2mSatake.mem_doubleCoset_iff (d g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) (v.adicCompletion K))) * localIntegralSet K v ↔
      ∃ a ∈ localIntegralSet K v, ∃ b ∈ localIntegralSet K v, a * d * b = g := by
  constructor
  · intro hg
    obtain ⟨p, hp, b, hb, rfl⟩ := Set.mem_mul.1 hg
    obtain ⟨a, ha, d', hd', rfl⟩ := Set.mem_mul.1 hp
    rw [Set.mem_singleton_iff] at hd'
    subst hd'
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Set.mem_mul.2 ⟨a * d, Set.mem_mul.2 ⟨a, ha, d, Set.mem_singleton d, rfl⟩, b, hb, rfl⟩

p2m_export "P2mSatake" "mem_doubleCoset_iff"

theorem conj_mem_doubleCoset_iff (d : GL (Fin 2) (v.adicCompletion K)) {k g : GL (Fin 2) (v.adicCompletion K)}
    (hk : k ∈ localIntegralSet K v) :
    k⁻¹ * g * k ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) (v.adicCompletion K))) * localIntegralSet K v ↔
      g ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) (v.adicCompletion K))) * localIntegralSet K v := by
  rw [mem_doubleCoset_iff, mem_doubleCoset_iff]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨k * a, mul_mem_localIntegralSet K v hk ha, b * k⁻¹,
      mul_mem_localIntegralSet K v hb (inv_mem_localIntegralSet K v hk), ?_⟩
    calc k * a * d * (b * k⁻¹) = k * (a * d * b) * k⁻¹ := by group
      _ = g := by rw [h]; group
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨k⁻¹ * a, mul_mem_localIntegralSet K v (inv_mem_localIntegralSet K v hk) ha, b * k,
      mul_mem_localIntegralSet K v hb hk, by group⟩

theorem coe_integralSubgroup_eq_localIntegralSet :
    ((integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
        Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) =
      localIntegralSet K v := by
  ext g
  have hinj : Function.Injective
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := Subtype.val_injective
  have hrange : Set.range (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := Subtype.range_val
  rw [SetLike.mem_coe, FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem hinj, mem_localIntegralSet]
  simp only [hrange, SetLike.mem_coe]

theorem exists_units_coe_eq_mul_zpow_log {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ)
    {x : v.adicCompletion K} (hx : x ≠ 0) :
    ∃ e : (v.adicCompletionIntegers K)ˣ,
      ((e : v.adicCompletionIntegers K) : v.adicCompletion K) =
        x * ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ WithZero.log (Valued.v x) := by
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hπ := valued_uniformiser K v hϖ
  set L : ℤ := WithZero.log (Valued.v x) with hL
  have hx' : Valued.v x = WithZero.exp L := (WithZero.exp_log hvx).symm
  have hval : Valued.v (x * ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ L) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hx', ← WithZero.exp_zsmul, zsmul_eq_mul, Int.cast_id, mul_neg_one,
      ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have hmem : x * ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ L ∈ v.adicCompletionIntegers K :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hval.le
  obtain ⟨e, he⟩ := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
    (a := (⟨_, hmem⟩ : v.adicCompletionIntegers K))).2 hval
  exact ⟨e, congrArg Subtype.val he⟩

end Local

section Outer

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

attribute [local instance] AutomorphicForm.locallyCompactSpace_localGL AutomorphicForm.localGLBorel
  AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar

theorem measurableSet_localIntegralSet : MeasurableSet (localIntegralSet K v) :=
  (isOpen_localIntegralSet K v).measurableSet

theorem integral_indicator_mul_eq_of_forall_eq {Φ : GL (Fin 2) (v.adicCompletion K) → ℂ} {C : ℂ}
    (hΦ : ∀ k ∈ localIntegralSet K v, Φ k = C) :
    ∫ k, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k * Φ k ∂(localHaar K v) = C := by
  have hfun : (fun k => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k * Φ k) =
      (localIntegralSet K v).indicator (fun _ => C) := by
    ext k
    by_cases hk : k ∈ localIntegralSet K v
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk, one_mul, hΦ k hk]
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, zero_mul]
  rw [hfun, integral_indicator_const _ (measurableSet_localIntegralSet K v), measureReal_def,
    localHaar_localIntegralSet, ENNReal.toReal_one, one_smul]

end Outer

section Walk

def walk (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => (q + 1) * walk q k 1
  | k + 1, d + 1 => walk q k d + q * walk q k (d + 2)

theorem walk_zero_zero (q : ℕ) : walk q 0 0 = 1 := by simp [walk]
theorem walk_zero_succ (q d : ℕ) : walk q 0 (d + 1) = 0 := by simp [walk]
theorem walk_succ_zero (q k : ℕ) : walk q (k + 1) 0 = (q + 1) * walk q k 1 := by simp [walk]
theorem walk_succ_succ (q k d : ℕ) : walk q (k + 1) (d + 1) = walk q k d + q * walk q k (d + 2) := by
  simp [walk]

theorem walk_eq_zero_of_lt (q : ℕ) : ∀ k d : ℕ, k < d → walk q k d = 0 := by
  intro k
  induction k with
  | zero =>
    intro d hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    exact walk_zero_succ q d'
  | succ k ih =>
    intro d hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [walk_succ_succ, ih d' (by omega), ih (d' + 2) (by omega), mul_zero, add_zero]

end Walk

section Word

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "M2" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

theorem exists_unit_eq_mul_zpow_of_norm_eq {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ)
    {x : Kv} {m : ℤ} (hx : ‖x‖ = ‖(ϖ : Kv)‖ ^ m) :
    ∃ e : (v.adicCompletionIntegers K)ˣ, x = ((e : v.adicCompletionIntegers K) : Kv) * (ϖ : Kv) ^ m := by
  have hπ0 := uniformiser_ne_zero K v hϖ
  have hπpos := norm_uniformiser_pos K v hϖ
  have hx0 : x ≠ 0 := by
    rw [← norm_pos_iff, hx]; exact zpow_pos hπpos m
  obtain ⟨L, hL, hnorm⟩ := exists_valued_eq_exp_and_norm_eq K v hx0
  have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm K v
  have hLm : L = -m := by
    have h1 : (Ideal.absNorm v.asIdeal : ℝ) ^ L = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m) := by
      rw [← hnorm, hx, norm_uniformiser K v hϖ, inv_zpow', ]
    exact zpow_right_injective₀ (by positivity) hN.ne' h1
  have hvx0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  have hlog : WithZero.log (Valued.v x) = -m := by rw [hL, WithZero.log_exp, hLm]
  obtain ⟨e, he⟩ := exists_units_coe_eq_mul_zpow_log K v hϖ hx0
  refine ⟨e, ?_⟩
  rw [he, hlog, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]

theorem conj_mem_heckeDoubleCoset {g x k₀ : GL (Fin 2) Kv}
    (hx : x ∈ doubleCoset (integralSubgroup (v.adicCompletionIntegers K) Kv) g)
    (hk₀ : k₀ ∈ integralSubgroup (v.adicCompletionIntegers K) Kv) :
    k₀⁻¹ * x * k₀ ∈ doubleCoset (integralSubgroup (v.adicCompletionIntegers K) Kv) g := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  refine HeckePair.mem_doubleCoset_iff.mpr ⟨k₀⁻¹ * u₁, mul_mem (inv_mem hk₀) hu₁, u₂ * k₀, mul_mem hu₂ hk₀, ?_⟩
  simp only [mul_assoc]

theorem comm_reassoc {G : Type*} [Group G] (A B C D E : G) (hAB : A * B = B * A) (hAC : A * C = C * A) :
    A * B * (C * D * E) = B * (C * (A * D) * E) := by
  calc A * B * (C * D * E) = B * A * (C * D * E) := by rw [hAB]
    _ = B * ((A * C) * D * E) := by simp only [mul_assoc]
    _ = B * ((C * A) * D * E) := by rw [hAC]
    _ = B * (C * (A * D) * E) := by simp only [mul_assoc]

theorem word_value
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) Kv)
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) (diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) Kv)
    (hz : (z : M2) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ • (1 : M2))
    (k j : ℕ) (a b : Kv) (m₁ m₂ : ℤ)
    (ha : ‖a‖ = ‖(ϖ : Kv)‖ ^ m₁) (hb : ‖b‖ = ‖(ϖ : Kv)‖ ^ m₂)
    (t : GL (Fin 2) Kv) (ht : (t : M2) = Matrix.diagonal ![a, b])
    {k₀ : GL (Fin 2) Kv} (hk₀ : k₀ ∈ localIntegralSet K v) (u : Kv)
    (c : ℤ) (hcM : c ≤ min m₁ m₂) (hle : ‖a * u‖ ≤ ‖(ϖ : Kv)‖ ^ c)
    (hcell : c = min m₁ m₂ ∨ ‖a * u‖ = ‖(ϖ : Kv)‖ ^ c) :
    ∑ ι : Fin k → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (k₀⁻¹ * (t * unipotentGL2 u) * k₀)) =
      if m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ) then
        (walk (Ideal.absNorm v.asIdeal) k (m₁ + m₂ - 2 * c).toNat : ℂ) else 0 := by
  classical
  have hπ0 : ((ϖ : v.adicCompletionIntegers K) : Kv) ≠ 0 := hϖ0
  have hπpos := norm_uniformiser_pos K v hϖ
  have hπ1 := norm_uniformiser_lt_one K v hϖ
  haveI : Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) :=
    Finite.of_equiv (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
      (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq).toEquiv
  have hq := natCard_quotient_span_uniformiser K v hϖ

  have hzc : ∀ g : GL (Fin 2) Kv, Commute z g := central_of_coe_eq_smul hz
  have hscπ : sc Kv (Units.mk0 _ hϖ0) = z := sc_mk0_eq_of_coe ϖ hϖ0 hz

  obtain ⟨e₁, he₁⟩ := exists_unit_eq_mul_zpow_of_norm_eq K v hϖ ha
  obtain ⟨e₂, he₂⟩ := exists_unit_eq_mul_zpow_of_norm_eq K v hϖ hb

  set w : Kvˣ := (Units.mk0 _ hϖ0) ^ (-(j : ℤ)) with hw
  have hwval : (w : Kv) = (ϖ : Kv) ^ (-(j : ℤ)) := by
    rw [hw, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rfl
  have hzj : (z ^ j)⁻¹ = sc Kv w := by
    rw [← hscπ, ← map_pow, ← map_inv, hw, ← zpow_natCast, zpow_neg]
  set y' : GL (Fin 2) Kv := sc Kv w * (t * unipotentGL2 u) with hy'
  have hy'coe : (y' : M2) = !![(w : Kv) * a, (w : Kv) * a * u; 0, (w : Kv) * b] := by
    have hdiag : (Matrix.diagonal ![a, b] : M2) = !![a, 0; 0, b] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hsc : ((sc Kv w : GL (Fin 2) Kv) : M2) = !![(w : Kv), 0; 0, (w : Kv)] := by
      rw [coe_sc]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hy', Units.val_mul, Units.val_mul, hsc, ht, hdiag, unipotentGL2_coe, Matrix.mul_fin_two,
      Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_assoc]
  have e00 : (y' : M2) 0 0 = (w : Kv) * a := by rw [hy'coe]; simp
  have e01 : (y' : M2) 0 1 = (w : Kv) * a * u := by rw [hy'coe]; simp
  have e10 : (y' : M2) 1 0 = 0 := by rw [hy'coe]; simp
  have e11 : (y' : M2) 1 1 = (w : Kv) * b := by rw [hy'coe]; simp
  have h00 : (y' : M2) 0 0 = algebraMap (v.adicCompletionIntegers K) Kv e₁ *
      algebraMap (v.adicCompletionIntegers K) Kv ϖ ^ (m₁ - j) := by
    rw [e00, hwval, he₁]
    show (ϖ : Kv) ^ (-(j : ℤ)) * (((e₁ : v.adicCompletionIntegers K) : Kv) * (ϖ : Kv) ^ m₁) =
      ((e₁ : v.adicCompletionIntegers K) : Kv) * (ϖ : Kv) ^ (m₁ - (j : ℤ))
    rw [zpow_sub₀ hπ0, zpow_neg, zpow_natCast]
    ring
  have h10 : (y' : M2) 1 0 = 0 := e10
  have h11 : (y' : M2) 1 1 = algebraMap (v.adicCompletionIntegers K) Kv e₂ *
      algebraMap (v.adicCompletionIntegers K) Kv ϖ ^ (m₂ - j) := by
    rw [e11, hwval, he₂]
    show (ϖ : Kv) ^ (-(j : ℤ)) * (((e₂ : v.adicCompletionIntegers K) : Kv) * (ϖ : Kv) ^ m₂) =
      ((e₂ : v.adicCompletionIntegers K) : Kv) * (ϖ : Kv) ^ (m₂ - (j : ℤ))
    rw [zpow_sub₀ hπ0, zpow_neg, zpow_natCast]
    ring
  have h01 : (y' : M2) 0 1 = (ϖ : Kv) ^ (-(j : ℤ)) * (a * u) := by
    rw [e01, hwval]; ring
  have hnorm01 : ‖(y' : M2) 0 1‖ = ‖(ϖ : Kv)‖ ^ (-(j : ℤ)) * ‖a * u‖ := by
    rw [h01, norm_mul, norm_zpow]

  have hmem : y' ∈ doubleCoset (integralSubgroup (v.adicCompletionIntegers K) Kv)
      (diagPi ϖ hϖ0 ^ (c - j) * localRepInf ϖ hϖ0 ^ (m₁ + m₂ - j - c)) := by
    have hmn : c - (j : ℤ) ≤ m₁ + m₂ - j - c := by
      have := min_le_left m₁ m₂; have := min_le_right m₁ m₂; omega
    refine (LocalGL2.mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular hϖ hϖ0 y'
      e₁ e₂ (m₁ - j) (m₂ - j) h00 h10 h11 hmn).2 ⟨by ring, ?_, ?_, ?_⟩
    · simp only [le_min_iff, min_le_iff] at hcM ⊢
      have := min_le_left m₁ m₂; have := min_le_right m₁ m₂; omega
    · refine ⟨⟨(ϖ : Kv) ^ (-(c - (j : ℤ))) * (y' : M2) 0 1, ?_⟩, ?_⟩
      · rw [mem_integers_iff_norm, norm_mul, hnorm01, norm_zpow, ← mul_assoc, ← zpow_add₀ hπpos.ne',
          show -(c - (j : ℤ)) + -(j : ℤ) = -c by ring]
        calc ‖(ϖ : Kv)‖ ^ (-c) * ‖a * u‖ ≤ ‖(ϖ : Kv)‖ ^ (-c) * ‖(ϖ : Kv)‖ ^ c :=
              mul_le_mul_of_nonneg_left hle (zpow_nonneg hπpos.le _)
          _ = 1 := by rw [← zpow_add₀ hπpos.ne', neg_add_cancel, zpow_zero]
      · show (y' : M2) 0 1 = (ϖ : Kv) ^ (c - (j : ℤ)) * ((ϖ : Kv) ^ (-(c - (j : ℤ))) * (y' : M2) 0 1)
        rw [← mul_assoc, ← zpow_add₀ hπ0, add_neg_cancel, zpow_zero, one_mul]
    · intro hlt ⟨r, hr'⟩
      have hr : (y' : M2) 0 1 = (ϖ : Kv) ^ (c - (j : ℤ) + 1) * ((r : v.adicCompletionIntegers K) : Kv) := hr'
      have hcne : c ≠ min m₁ m₂ := by
        simp only [lt_min_iff] at hlt
        rcases le_total m₁ m₂ with h | h
        · rw [min_eq_left h]; omega
        · rw [min_eq_right h]; omega
      have heq : ‖a * u‖ = ‖(ϖ : Kv)‖ ^ c := hcell.resolve_left hcne
      have h1 : ‖(y' : M2) 0 1‖ ≤ ‖(ϖ : Kv)‖ ^ (c - (j : ℤ) + 1) := by
        rw [hr, norm_mul]
        calc ‖(ϖ : Kv) ^ (c - (j : ℤ) + 1)‖ * ‖((r : v.adicCompletionIntegers K) : Kv)‖
            ≤ ‖(ϖ : Kv) ^ (c - (j : ℤ) + 1)‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_coe_integer_le_one K v r) (norm_nonneg _)
          _ = ‖(ϖ : Kv)‖ ^ (c - (j : ℤ) + 1) := by rw [mul_one, norm_zpow]
      have h2 : ‖(y' : M2) 0 1‖ = ‖(ϖ : Kv)‖ ^ (c - (j : ℤ)) := by
        rw [hnorm01, heq, ← zpow_add₀ hπpos.ne']; congr 1; ring
      rw [h2] at h1
      exact absurd h1 (not_le.2 (zpow_lt_zpow_right_of_lt_one₀ hπpos hπ1 (lt_add_one _)))

  have hk₀' : k₀ ∈ integralSubgroup (v.adicCompletionIntegers K) Kv := by
    rw [← SetLike.mem_coe, coe_integralSubgroup_eq_localIntegralSet]; exact hk₀
  have hmem' := conj_mem_heckeDoubleCoset K v hmem hk₀'
  have hgen := LocalGL2.sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow
    ϖ hϖ0 hϖ rT hrT (walk (Ideal.absNorm v.asIdeal)) (walk_zero_zero _) (walk_zero_succ _)
    (fun k => by rw [hq]; exact walk_succ_zero _ k) (fun k d => by rw [hq]; exact walk_succ_succ _ k d)
    k (c - j) (m₁ + m₂ - j - c) (k₀⁻¹ * y' * k₀) hmem'
  have hiff : (c - (j : ℤ) + (m₁ + m₂ - j - c) = k) ↔ (m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ)) := by
    constructor <;> intro h <;> linarith
  have habs : (c - (j : ℤ) - (m₁ + m₂ - j - c)).natAbs = (m₁ + m₂ - 2 * c).toNat := by
    have h0 : 0 ≤ m₁ + m₂ - 2 * c := by
      have := min_le_left m₁ m₂; have := min_le_right m₁ m₂; omega
    have h1 : c - (j : ℤ) - (m₁ + m₂ - j - c) = -(m₁ + m₂ - 2 * c) := by ring
    rw [h1, Int.natAbs_neg]
    omega
  rw [habs] at hgen

  have hrhs : (if m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ) then
        (walk (Ideal.absNorm v.asIdeal) k (m₁ + m₂ - 2 * c).toNat : ℂ) else 0) =
      ((if c - (j : ℤ) + (m₁ + m₂ - j - c) = k then
        walk (Ideal.absNorm v.asIdeal) k (m₁ + m₂ - 2 * c).toNat else 0 : ℕ) : ℂ) := by
    by_cases h : m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ)
    · rw [if_pos h, if_pos (hiff.2 h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.1 h')), Nat.cast_zero]
  rw [hrhs, ← hgen, Nat.cast_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  have hg : ((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (k₀⁻¹ * (t * unipotentGL2 u) * k₀) =
      ((List.ofFn fun i => rT (ι i)).prod)⁻¹ * (k₀⁻¹ * y' * k₀) := by
    rw [mul_inv_rev, hy', ← hzj]
    have hzc' : ∀ g : GL (Fin 2) Kv, Commute (z ^ j)⁻¹ g := fun g => ((hzc g).pow_left j).inv_left
    exact comm_reassoc ((z ^ j)⁻¹) (((List.ofFn fun i => rT (ι i)).prod)⁻¹) (k₀⁻¹) (t * unipotentGL2 u) k₀
      (hzc' (((List.ofFn fun i => rT (ι i)).prod)⁻¹)).eq (hzc' (k₀⁻¹)).eq
  rw [hg, ← coe_integralSubgroup_eq_localIntegralSet]
  by_cases hU : ((List.ofFn fun i => rT (ι i)).prod)⁻¹ * (k₀⁻¹ * y' * k₀) ∈
      ((integralSubgroup (v.adicCompletionIntegers K) Kv : Subgroup (GL (Fin 2) Kv)) : Set (GL (Fin 2) Kv))
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, Nat.cast_one]
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU, Nat.cast_zero]

end Word

section Cells

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "M2" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

def cell (ϖ : v.adicCompletionIntegers K) (a : Kv) (M c : ℤ) : Set Kv :=
  if c = M then {u : Kv | ‖a * u‖ ≤ ‖(ϖ : Kv)‖ ^ M} else {u : Kv | ‖a * u‖ = ‖(ϖ : Kv)‖ ^ c}

def coef (q k j : ℕ) (c : ℤ) : ℂ := (walk q k ((k : ℤ) + 2 * (j : ℤ) - 2 * c).toNat : ℂ)

def shellFn (ϖ : v.adicCompletionIntegers K) (a : Kv) (M : ℤ) (q k j : ℕ) (u : Kv) : ℂ :=
  ∑ c ∈ Finset.Icc (j : ℤ) M, coef q k j c * (cell K v ϖ a M c).indicator (fun _ => (1 : ℂ)) u

theorem exists_cell {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {a : Kv} (ha0 : a ≠ 0) (M : ℤ) (u : Kv) :
    ∃ c : ℤ, c ≤ M ∧ ‖a * u‖ ≤ ‖(ϖ : Kv)‖ ^ c ∧ (c = M ∨ ‖a * u‖ = ‖(ϖ : Kv)‖ ^ c) ∧
      ∀ c' : ℤ, c' ≤ M → (u ∈ cell K v ϖ a M c' ↔ c' = c) := by
  have hπpos := norm_uniformiser_pos K v hϖ
  have hπ1 := norm_uniformiser_lt_one K v hϖ
  by_cases hA : ‖a * u‖ ≤ ‖(ϖ : Kv)‖ ^ M
  · refine ⟨M, le_rfl, hA, Or.inl rfl, fun c' hc' => ?_⟩
    by_cases hcM : c' = M
    · subst hcM
      rw [cell, if_pos rfl]
      exact ⟨fun _ => rfl, fun _ => hA⟩
    · have hlt : c' < M := lt_of_le_of_ne hc' hcM
      simp only [cell, if_neg hcM, Set.mem_setOf_eq, hcM, iff_false]
      intro heq
      have : ‖(ϖ : Kv)‖ ^ M < ‖(ϖ : Kv)‖ ^ c' := zpow_lt_zpow_right_of_lt_one₀ hπpos hπ1 hlt
      rw [heq] at hA
      exact absurd hA (not_le.2 this)
  · push Not at hA
    have hau : a * u ≠ 0 := by
      intro h; rw [h, norm_zero] at hA; exact absurd hA (not_lt.2 (zpow_nonneg hπpos.le _))
    obtain ⟨c, hc⟩ := exists_norm_eq_zpow K v hϖ hau
    have hcM : c < M := by
      rw [hc] at hA; exact (zpow_lt_zpow_iff_right_of_lt_one₀ hπpos hπ1).1 hA
    refine ⟨c, hcM.le, hc.le, Or.inr hc, fun c' hc' => ?_⟩
    by_cases hc'M : c' = M
    · subst hc'M
      simp only [cell, if_pos rfl, Set.mem_setOf_eq]
      constructor
      · intro h; exact absurd h (not_le.2 hA)
      · intro h; omega
    · simp only [cell, if_neg hc'M, Set.mem_setOf_eq, hc]
      constructor
      · intro h
        exact (zpow_right_injective₀ hπpos (hπ1.ne)) h.symm ▸ rfl
      · intro h; rw [h]

theorem word_eq_shellFn
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) Kv)
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) (diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) Kv)
    (hz : (z : M2) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ • (1 : M2))
    (k j : ℕ) (a b : Kv) (m₁ m₂ : ℤ)
    (ha : ‖a‖ = ‖(ϖ : Kv)‖ ^ m₁) (hb : ‖b‖ = ‖(ϖ : Kv)‖ ^ m₂)
    (t : GL (Fin 2) Kv) (ht : (t : M2) = Matrix.diagonal ![a, b])
    {k₀ : GL (Fin 2) Kv} (hk₀ : k₀ ∈ localIntegralSet K v) (u : Kv) :
    ∑ ι : Fin k → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (k₀⁻¹ * (t * unipotentGL2 u) * k₀)) =
      if m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ) then
        shellFn K v ϖ a (min m₁ m₂) (Ideal.absNorm v.asIdeal) k j u else 0 := by
  classical
  have hπpos := norm_uniformiser_pos K v hϖ
  have ha0 : a ≠ 0 := by rw [← norm_pos_iff, ha]; exact zpow_pos hπpos _
  obtain ⟨c, hcM, hle, hcell, huniq⟩ := exists_cell K v hϖ ha0 (min m₁ m₂) u
  rw [word_value K v ϖ hϖ hϖ0 n rT hrT z hz k j a b m₁ m₂ ha hb t ht hk₀ u c hcM hle hcell]
  by_cases hind : m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ)
  · rw [if_pos hind, if_pos hind, shellFn]
    have hsum : ∑ c' ∈ Finset.Icc (j : ℤ) (min m₁ m₂),
        coef (Ideal.absNorm v.asIdeal) k j c' * (cell K v ϖ a (min m₁ m₂) c').indicator (fun _ => (1 : ℂ)) u =
        ∑ c' ∈ Finset.Icc (j : ℤ) (min m₁ m₂), if c' = c then coef (Ideal.absNorm v.asIdeal) k j c' else 0 := by
      refine Finset.sum_congr rfl fun c' hc' => ?_
      have hc'M : c' ≤ min m₁ m₂ := (Finset.mem_Icc.1 hc').2
      by_cases h : c' = c
      · rw [if_pos h, Set.indicator_of_mem ((huniq c' hc'M).2 h), mul_one]
      · rw [if_neg h, Set.indicator_of_notMem (fun hm => h ((huniq c' hc'M).1 hm)), mul_zero]
    rw [hsum, Finset.sum_ite_eq']
    by_cases hjc : (j : ℤ) ≤ c
    · rw [if_pos (Finset.mem_Icc.2 ⟨hjc, hcM⟩), coef, hind]
    · rw [if_neg (fun h => hjc (Finset.mem_Icc.1 h).1)]
      push Not at hjc
      have hlt : k < (m₁ + m₂ - 2 * c).toNat := by
        have : (k : ℤ) < m₁ + m₂ - 2 * c := by omega
        omega
      rw [walk_eq_zero_of_lt _ k _ hlt, Nat.cast_zero]
  · rw [if_neg hind, if_neg hind]

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

theorem cell_subset_ball {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {a : Kv} {ka : ℤ}
    (hka : ‖a‖ = ‖(ϖ : Kv)‖ ^ ka) (M c : ℤ) (hc : c ≤ M) :
    cell K v ϖ a M c ⊆ ball K v ϖ (c - ka) := by
  intro u hu
  rw [← setOf_norm_mul_le_eq_ball K v hϖ hka c, Set.mem_setOf_eq]
  by_cases h : c = M
  · simp only [cell, if_pos h, Set.mem_setOf_eq] at hu; rw [h]; exact hu
  · simp only [cell, if_neg h, Set.mem_setOf_eq] at hu; exact hu.le

theorem measurableSet_cell (ϖ : v.adicCompletionIntegers K) (a : Kv) (M c : ℤ) :
    MeasurableSet (cell K v ϖ a M c) := by
  have hcont : Continuous fun u : Kv => ‖a * u‖ := continuous_norm.comp (continuous_const.mul continuous_id)
  by_cases h : c = M
  · simp only [cell, if_pos h]
    exact (isClosed_le hcont continuous_const).measurableSet
  · simp only [cell, if_neg h]
    exact (isClosed_eq hcont continuous_const).measurableSet

theorem integral_shellFn {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {a : Kv} {ka : ℤ}
    (hka : ‖a‖ = ‖(ϖ : Kv)‖ ^ ka) (M : ℤ) (q k j : ℕ) (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ∫ u, shellFn K v ϖ a M q k j u ∂ν =
      ∑ c ∈ Finset.Icc (j : ℤ) M, coef q k j c * (ν.real (cell K v ϖ a M c) : ℂ) := by
  have hint : ∀ c ∈ Finset.Icc (j : ℤ) M,
      Integrable (fun u => coef q k j c * (cell K v ϖ a M c).indicator (fun _ => (1 : ℂ)) u) ν := by
    intro c hc
    refine Integrable.const_mul ?_ _
    refine (integrable_indicator_iff (measurableSet_cell K v ϖ a M c)).2 ?_
    refine integrableOn_const ?_
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (cell_subset_ball K v hϖ hka M c (Finset.mem_Icc.1 hc).2)) ?_)
    exact measure_ball_lt_top K v ϖ _ ν
  unfold shellFn
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [integral_const_mul, integral_indicator_const _ (measurableSet_cell K v ϖ a M c), Complex.real_smul, mul_one]

theorem norm_mul_measureReal_cell {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) {a : Kv} (ha0 : a ≠ 0)
    (M c : ℤ) (ν : Measure Kv) [ν.IsAddHaarMeasure] :
    ‖a‖ * ν.real (cell K v ϖ a M c) =
      ‖(ϖ : Kv)‖ ^ c * (if c = M then 1 else (1 - ‖(ϖ : Kv)‖)) *
        ν.real (v.adicCompletionIntegers K : Set Kv) := by
  by_cases h : c = M
  · simp only [cell, if_pos h, mul_one]
    rw [h]; exact norm_mul_measureReal_setOf_norm_mul_le K v hϖ ha0 M ν
  · simp only [cell, if_neg h]
    exact norm_mul_measureReal_setOf_norm_mul_eq K v hϖ ha0 c ν

end Cells

section Arith

theorem sum_cells_eq_choose (q : ℕ) (hq : 0 < q) (k j μ : ℕ) (hk : 2 * μ ≤ k) :
    (q : ℂ) ^ j * ∑ c ∈ Finset.Icc (j : ℤ) ((j : ℤ) + μ),
        (walk q k (((k : ℤ) + 2 * (j : ℤ) - 2 * c).toNat) : ℂ) *
          (((q : ℂ)⁻¹) ^ c * (if c = (j : ℤ) + μ then 1 else (1 - (q : ℂ)⁻¹))) =
      ((k.choose μ : ℕ) : ℂ) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  set x : ℂ := (q : ℂ)⁻¹ with hx
  have hx0 : x ≠ 0 := inv_ne_zero hq0
  have hqx : (q : ℂ) * x = 1 := mul_inv_cancel₀ hq0

  rw [← Finset.Ico_insert_right (by omega : (j : ℤ) ≤ (j : ℤ) + μ), Finset.sum_insert Finset.right_notMem_Ico,
    if_pos rfl, mul_one]

  have hlow : ∑ c ∈ Finset.Ico (j : ℤ) ((j : ℤ) + μ),
      (walk q k (((k : ℤ) + 2 * (j : ℤ) - 2 * c).toNat) : ℂ) *
        (x ^ c * (if c = (j : ℤ) + μ then 1 else (1 - x))) =
      ∑ r ∈ Finset.range μ, (walk q k (k - 2 * r) : ℂ) * (x ^ ((j : ℤ) + r) * (1 - x)) := by
    refine Finset.sum_nbij' (fun c => (c - j).toNat) (fun r => (j : ℤ) + r) ?_ ?_ ?_ ?_ ?_
    · intro c hc; simp only [Finset.mem_Ico] at hc; simp only [Finset.mem_range]; omega
    · intro r hr; simp only [Finset.mem_range] at hr; simp only [Finset.mem_Ico]; omega
    · intro c hc; simp only [Finset.mem_Ico] at hc; show (j : ℤ) + (((c - (j : ℤ)).toNat : ℕ) : ℤ) = c; omega
    · intro r hr; show (((j : ℤ) + (r : ℕ) - (j : ℤ)).toNat) = r; omega
    · intro c hc
      simp only [Finset.mem_Ico] at hc
      have hne : c ≠ (j : ℤ) + μ := by omega
      rw [if_neg hne]
      have h1 : ((k : ℤ) + 2 * (j : ℤ) - 2 * c).toNat = k - 2 * (c - j).toNat := by omega
      have h2 : ((j : ℤ) + ((c - (j : ℤ)).toNat : ℕ)) = c := by omega
      rw [h1, h2]
  rw [hlow]
  have htop : ((k : ℤ) + 2 * (j : ℤ) - 2 * ((j : ℤ) + μ)).toNat = k - 2 * μ := by omega
  rw [htop]

  have hpow : ∀ r : ℕ, (q : ℂ) ^ j * x ^ ((j : ℤ) + r) = x ^ r := by
    intro r
    rw [zpow_add₀ hx0, zpow_natCast, zpow_natCast, ← mul_assoc, ← mul_pow, hqx, one_pow, one_mul]
  have hpow' : (q : ℂ) ^ j * x ^ ((j : ℤ) + μ) = x ^ μ := by exact_mod_cast hpow μ
  rw [mul_add, Finset.mul_sum]
  have hre : ∀ r ∈ Finset.range μ, (q : ℂ) ^ j * ((walk q k (k - 2 * r) : ℂ) * (x ^ ((j : ℤ) + r) * (1 - x))) =
      (walk q k (k - 2 * r) : ℂ) * (x ^ r * (1 - x)) := by
    intro r _
    rw [← hpow r]; ring
  rw [Finset.sum_congr rfl hre, show (q : ℂ) ^ j * ((walk q k (k - 2 * μ) : ℂ) * x ^ ((j : ℤ) + ↑μ)) =
    (walk q k (k - 2 * μ) : ℂ) * x ^ μ by rw [← hpow']; ring]

  have hT := HeckeTreeWalk.cast_walkCount_add_sum_mul_pow_sub_pow_eq_choose_mul_pow q (walk q)
    (walk_zero_zero q) (walk_zero_succ q) (walk_succ_zero q) (walk_succ_succ q) (k - 2 * μ) μ
  have hkd : k - 2 * μ + 2 * μ = k := by omega
  rw [hkd] at hT
  have hT' : ((walk q k (k - 2 * μ) : ℤ) : ℂ) +
      ∑ r ∈ Finset.range μ, ((walk q k (k - 2 * μ + 2 * (r + 1)) : ℤ) : ℂ) * ((q : ℂ) ^ (r + 1) - (q : ℂ) ^ r) =
      ((k.choose μ : ℕ) : ℂ) * (q : ℂ) ^ μ := by exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hT

  have hrefl : ∑ r ∈ Finset.range μ, (walk q k (k - 2 * r) : ℂ) * (x ^ r * (1 - x)) =
      x ^ μ * ∑ r ∈ Finset.range μ, ((walk q k (k - 2 * μ + 2 * (r + 1)) : ℤ) : ℂ) * ((q : ℂ) ^ (r + 1) - (q : ℂ) ^ r) := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [Finset.mem_range] at hr
    have h1 : k - 2 * (μ - 1 - r) = k - 2 * μ + 2 * (r + 1) := by omega
    rw [h1]
    push_cast

    have e1 : x ^ (r + 1) * (q : ℂ) ^ (r + 1) = 1 := by rw [← mul_pow, mul_comm, hqx, one_pow]
    have e2 : x ^ (r + 1) * (q : ℂ) ^ r = x := by
      rw [pow_succ', mul_assoc, ← mul_pow, mul_comm x (q : ℂ), hqx, one_pow, mul_one]
    have hμ : μ = (μ - 1 - r) + (r + 1) := by omega
    have h2 : x ^ μ * ((q : ℂ) ^ (r + 1) - (q : ℂ) ^ r) = x ^ (μ - 1 - r) * (1 - x) := by
      calc x ^ μ * ((q : ℂ) ^ (r + 1) - (q : ℂ) ^ r)
          = x ^ (μ - 1 - r) * x ^ (r + 1) * ((q : ℂ) ^ (r + 1) - (q : ℂ) ^ r) := by rw [← pow_add, ← hμ]
        _ = x ^ (μ - 1 - r) * (x ^ (r + 1) * (q : ℂ) ^ (r + 1) - x ^ (r + 1) * (q : ℂ) ^ r) := by ring
        _ = x ^ (μ - 1 - r) * (1 - x) := by rw [e1, e2]
    calc ((walk q k (k - 2 * μ + 2 * (r + 1)) : ℕ) : ℂ) * (x ^ (μ - 1 - r) * (1 - x))
        = ((walk q k (k - 2 * μ + 2 * (r + 1)) : ℕ) : ℂ) * (x ^ μ * ((q : ℂ) ^ (r + 1) - (q : ℂ) ^ r)) := by rw [h2]
      _ = x ^ μ * ((((walk q k (k - 2 * μ + 2 * (r + 1)) : ℕ) : ℤ) : ℂ) * ((q : ℂ) ^ (r + 1) - (q : ℂ) ^ r)) := by
          push_cast; ring
  rw [hrefl]
  have hxq : x ^ μ * (q : ℂ) ^ μ = 1 := by rw [← mul_pow, mul_comm, hqx, one_pow]
  calc (walk q k (k - 2 * μ) : ℂ) * x ^ μ +
        x ^ μ * ∑ r ∈ Finset.range μ, ((walk q k (k - 2 * μ + 2 * (r + 1)) : ℤ) : ℂ) * ((q : ℂ) ^ (r + 1) - (q : ℂ) ^ r)
      = x ^ μ * (((walk q k (k - 2 * μ) : ℤ) : ℂ) +
          ∑ r ∈ Finset.range μ, ((walk q k (k - 2 * μ + 2 * (r + 1)) : ℤ) : ℂ) * ((q : ℂ) ^ (r + 1) - (q : ℂ) ^ r)) := by
        push_cast; ring
    _ = ((k.choose μ : ℕ) : ℂ) := by rw [hT', mul_comm, mul_assoc, mul_comm ((q:ℂ)^μ), hxq, mul_one]

theorem laurent_eval (k j : ℕ) (m₁ m₂ : ℤ) (hind : m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ)) :
    (∑ i ∈ Finset.range (k + 1), if (2 * (i : ℤ) - k = m₁ - m₂) then ((k.choose i : ℕ) : ℂ) else 0) =
      if (j : ℤ) ≤ min m₁ m₂ then ((k.choose (min m₁ m₂ - j).toNat : ℕ) : ℂ) else 0 := by
  by_cases hjM : (j : ℤ) ≤ min m₁ m₂
  · rw [if_pos hjM]
    have hm1 := min_le_left m₁ m₂
    have hm2 := min_le_right m₁ m₂

    set i₀ : ℕ := if m₁ ≤ m₂ then (min m₁ m₂ - j).toNat else k - (min m₁ m₂ - j).toNat with hi₀
    have hi₀k : i₀ ≤ k := by
      rw [hi₀]; split_ifs <;> [skip; omega]
      rcases le_total m₁ m₂ with h | h
      · rw [min_eq_left h]; omega
      · rw [min_eq_right h] at *; omega
    have hi₀eq : 2 * (i₀ : ℤ) - k = m₁ - m₂ := by
      rw [hi₀]
      split_ifs with h
      · rw [min_eq_left h]; push_cast; omega
      · push Not at h
        have hmin : min m₁ m₂ = m₂ := min_eq_right h.le
        rw [hmin] at hjM ⊢
        have : (m₂ - (j : ℤ)).toNat ≤ k := by omega
        push_cast [this]
        omega
    have hchoose : k.choose i₀ = k.choose (min m₁ m₂ - j).toNat := by
      rw [hi₀]
      split_ifs with h
      · rfl
      · rw [Nat.choose_symm]
        rcases le_total m₁ m₂ with h' | h'
        · exact absurd h' h
        · rw [min_eq_right h']; omega
    rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_range.2 (by omega))]
    · rw [if_pos hi₀eq, hchoose]
    · intro i _ hne
      rw [if_neg]
      intro h
      apply hne
      have : (2 * (i : ℤ)) = 2 * (i₀ : ℤ) := by omega
      exact_mod_cast (mul_right_injective₀ (two_ne_zero' ℤ) this)
  · rw [if_neg hjM]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_neg]
    intro h
    simp only [Finset.mem_range] at hi
    push Not at hjM
    rcases le_total m₁ m₂ with h' | h'
    · rw [min_eq_left h'] at hjM; omega
    · rw [min_eq_right h'] at hjM; omega

end Arith

section Assembly

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "M2" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

theorem isLocalTestFn_indicator_translate (g : GL (Fin 2) Kv) :
    IsLocalTestFn K v (fun x => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (g * x)) := by
  have h := isLocalTestFn_indicator_localIntegralSet K v
  refine ⟨?_, ?_⟩
  · exact h.1.comp_continuous (continuous_mul_left g)
  · have : (fun x => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (g * x)) =
        (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) ∘ (Homeomorph.mulLeft g) := rfl
    rw [this]
    exact h.2.comp_homeomorph _

theorem isLocalTestFn_sum {ι : Type*} (s : Finset ι) (F : ι → GL (Fin 2) Kv → ℂ)
    (hF : ∀ i ∈ s, IsLocalTestFn K v (F i)) :
    IsLocalTestFn K v (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLocalTestFn_zero K v
  | insert i s hi ih =>
    have h1 := hF i (Finset.mem_insert_self i s)
    have h2 := ih (fun i' hi' => hF i' (Finset.mem_insert_of_mem hi'))
    have : (fun x => ∑ i' ∈ insert i s, F i' x) = (fun x => F i x) + fun x => ∑ i' ∈ s, F i' x := by
      funext x; rw [Finset.sum_insert hi]; rfl
    rw [this]
    exact ⟨h1.1.add h2.1, h1.2.add h2.2⟩

theorem main
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)
    (a b : v.adicCompletion K) (hab : a ≠ b) (m₁ m₂ : ℤ)
    (ha : ‖a‖ = ‖(ϖ : v.adicCompletion K)‖ ^ m₁) (hb : ‖b‖ = ‖(ϖ : v.adicCompletion K)‖ ^ m₂)
    (t : GL (Fin 2) (v.adicCompletion K))
    (ht : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![a, b])
    (τ : @Measure (AutomorphicForm.localCentralizer K v t) (AutomorphicForm.localCentralizerBorel K v t))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v t) τ)
    (hτ1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegral K v t τ
      (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * x)) I) :
    ((‖a - b‖ : ℝ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ j * I =
      if m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ) then
        ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff (m₁ - m₂)
      else 0 := by
  classical
  letI mKv : MeasurableSpace Kv := borel Kv
  haveI : BorelSpace Kv := ⟨rfl⟩
  set ν : Measure Kv := Measure.addHaar with hν
  have hπ0 : ((ϖ : v.adicCompletionIntegers K) : Kv) ≠ 0 := hϖ0
  have hπpos := norm_uniformiser_pos K v hϖ
  have hπ1 := norm_uniformiser_lt_one K v hϖ
  have ha0 : a ≠ 0 := by rw [← norm_pos_iff, ha]; exact zpow_pos hπpos _
  have hab0 : ‖a - b‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hab)
  have hna0 : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha0

  have hdiag : (Matrix.diagonal ![a, b] : M2) = !![a, 0; 0, b] := by
    ext i j'; fin_cases i <;> fin_cases j' <;> simp
  have ht00 : (t : M2) 0 0 = a := by rw [ht, hdiag]; simp
  have ht01 : (t : M2) 0 1 = 0 := by rw [ht, hdiag]; simp
  have ht10 : (t : M2) 1 0 = 0 := by rw [ht, hdiag]; simp
  have ht11 : (t : M2) 1 1 = b := by rw [ht, hdiag]; simp

  have hreg : IsRegularSemisimple t := by
    rw [isRegularSemisimple_iff_ne_zero, Matrix.trace_fin_two, Matrix.det_fin_two, ht00, ht01, ht10, ht11]
    have : (a + b) ^ 2 - 4 * (a * b - 0 * 0) = (a - b) ^ 2 := by ring
    rw [this]
    exact pow_ne_zero 2 (sub_ne_zero.2 hab)

  have hf : IsLocalTestFn K v (fun x : GL (Fin 2) Kv =>
      ∑ ι : Fin k → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * x)) :=
    isLocalTestFn_sum K v Finset.univ _ (fun ι _ => isLocalTestFn_indicator_translate K v _)

  have hred := AutomorphicForm.eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
    K v t hreg ht01 ht10 τ hτ ν _ hf I hI

  set M : ℤ := min m₁ m₂ with hM
  set q : ℕ := Ideal.absNorm v.asIdeal with hq
  set J : ℂ := if m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ) then
      ∑ c ∈ Finset.Icc (j : ℤ) M, coef q k j c * (ν.real (cell K v ϖ a M c) : ℂ) else 0 with hJ
  have hinner : ∀ k₀ ∈ localIntegralSet K v,
      (∫ u, (fun x : GL (Fin 2) Kv => ∑ ι : Fin k → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * x)) (k₀⁻¹ * (t * unipotentGL2 u) * k₀) ∂ν) = J := by
    intro k₀ hk₀
    have hfun : (fun u : Kv => (fun x : GL (Fin 2) Kv => ∑ ι : Fin k → Fin n,
        (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * x))
          (k₀⁻¹ * (t * unipotentGL2 u) * k₀)) =
        fun u => if m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ) then shellFn K v ϖ a M q k j u else 0 := by
      funext u
      exact word_eq_shellFn K v ϖ hϖ hϖ0 n rT hrT z hz k j a b m₁ m₂ ha hb t ht hk₀ u
    rw [hfun, hJ]
    split_ifs with hind
    · exact integral_shellFn K v hϖ ha M q k j ν
    · simp
  have houter := integral_indicator_mul_eq_of_forall_eq K v hinner
  rw [houter] at hred

  have hτ' : (τ {t' : localCentralizer K v t | (t' : GL (Fin 2) Kv) ∈ localIntegralSet K v}).toReal = 1 := by
    have : τ {t' : localCentralizer K v t | (t' : GL (Fin 2) Kv) ∈ localIntegralSet K v} = 1 := hτ1
    rw [this, ENNReal.toReal_one]
  have hν𝓞 : (ν (v.adicCompletionIntegers K : Set Kv)).toReal = ν.real (v.adicCompletionIntegers K : Set Kv) := rfl
  have hνpos : ν.real (v.adicCompletionIntegers K : Set Kv) ≠ 0 := by
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    constructor
    · have hopen : IsOpen (v.adicCompletionIntegers K : Set Kv) := by
        rw [coe_integers_eq_closedBall K v]
        exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero
      exact (hopen.measure_pos ν ⟨0, zero_mem _⟩).ne'
    · rw [← ball_zero K v ϖ]; exact (measure_ball_lt_top K v ϖ 0 ν).ne
  have hnorm : ‖1 - b / a‖ = ‖a - b‖ / ‖a‖ := by
    rw [one_sub_div ha0, norm_div]
  rw [hred, hτ', ht00, ht11, hν𝓞, hnorm, inv_one, one_mul]

  by_cases hind : m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ)
  · rw [if_pos hind, LaurentPolynomial.T_one_add_T_neg_one_pow_apply_eq_sum_ite_choose, laurent_eval k j m₁ m₂ hind,
      hJ, if_pos hind]

    have hmass : ∀ c ∈ Finset.Icc (j : ℤ) M, (ν.real (cell K v ϖ a M c) : ℂ) =
        ((‖a‖⁻¹ * ν.real (v.adicCompletionIntegers K : Set Kv) : ℝ) : ℂ) *
          (((‖(ϖ : Kv)‖ : ℝ) : ℂ) ^ c * (if c = M then 1 else (1 - ((‖(ϖ : Kv)‖ : ℝ) : ℂ)))) := by
      intro c _
      have h := norm_mul_measureReal_cell K v hϖ ha0 M c ν
      have h' : ν.real (cell K v ϖ a M c) = ‖a‖⁻¹ * ν.real (v.adicCompletionIntegers K : Set Kv) *
          (‖(ϖ : Kv)‖ ^ c * (if c = M then 1 else (1 - ‖(ϖ : Kv)‖))) := by
        field_simp
        linear_combination h
      rw [h']
      push_cast
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl (fun c hc => by rw [hmass c hc])]
    have hfac : ∑ c ∈ Finset.Icc (j : ℤ) M, coef q k j c *
        (((‖a‖⁻¹ * ν.real (v.adicCompletionIntegers K : Set Kv) : ℝ) : ℂ) *
          (((‖(ϖ : Kv)‖ : ℝ) : ℂ) ^ c * (if c = M then 1 else (1 - ((‖(ϖ : Kv)‖ : ℝ) : ℂ))))) =
        ((‖a‖⁻¹ * ν.real (v.adicCompletionIntegers K : Set Kv) : ℝ) : ℂ) *
          ∑ c ∈ Finset.Icc (j : ℤ) M, coef q k j c *
            (((‖(ϖ : Kv)‖ : ℝ) : ℂ) ^ c * (if c = M then 1 else (1 - ((‖(ϖ : Kv)‖ : ℝ) : ℂ)))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hfac]

    have hscal : ((‖a - b‖ : ℝ) : ℂ) * (q : ℂ) ^ j *
        ((((ν.real (v.adicCompletionIntegers K : Set Kv))⁻¹ * (‖a - b‖ / ‖a‖)⁻¹ : ℝ) : ℂ) *
          (((‖a‖⁻¹ * ν.real (v.adicCompletionIntegers K : Set Kv) : ℝ) : ℂ) *
            ∑ c ∈ Finset.Icc (j : ℤ) M, coef q k j c *
              (((‖(ϖ : Kv)‖ : ℝ) : ℂ) ^ c * (if c = M then 1 else (1 - ((‖(ϖ : Kv)‖ : ℝ) : ℂ)))))) =
        (q : ℂ) ^ j * ∑ c ∈ Finset.Icc (j : ℤ) M, coef q k j c *
              (((‖(ϖ : Kv)‖ : ℝ) : ℂ) ^ c * (if c = M then 1 else (1 - ((‖(ϖ : Kv)‖ : ℝ) : ℂ)))) := by
      have h1 : ((‖a - b‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hab0
      have h2 : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hna0
      have h3 : ((ν.real (v.adicCompletionIntegers K : Set Kv) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνpos
      push_cast
      field_simp
    rw [hscal]

    have hπq : ((‖(ϖ : Kv)‖ : ℝ) : ℂ) = (q : ℂ)⁻¹ := by
      rw [norm_uniformiser K v hϖ, hq]; push_cast; rfl
    rw [hπq]
    by_cases hjM : (j : ℤ) ≤ M
    · rw [if_pos hjM]
      obtain ⟨μ, hμ⟩ : ∃ μ : ℕ, M = (j : ℤ) + μ := ⟨(M - j).toNat, by omega⟩
      have hk2 : 2 * μ ≤ k := by
        have := min_le_left m₁ m₂; have := min_le_right m₁ m₂; omega
      have hμ' : (M - (j : ℤ)).toNat = μ := by omega
      rw [hμ', hμ]
      have hqpos : 0 < q := by
        have := one_lt_absNorm K v
        rw [hq]; exact_mod_cast (zero_lt_one.trans this)
      exact sum_cells_eq_choose q hqpos k j μ hk2
    · rw [if_neg hjM, Finset.Icc_eq_empty (by omega), Finset.sum_empty, mul_zero]
  · rw [if_neg hind, hJ, if_neg hind, mul_zero, mul_zero]

end Assembly

end P2mSatake

end

open MeasureTheory NumberField IsDedekindDomain in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)
    (a b : v.adicCompletion K) (hab : a ≠ b) (m₁ m₂ : ℤ)
    (ha : ‖a‖ = ‖(ϖ : v.adicCompletion K)‖ ^ m₁) (hb : ‖b‖ = ‖(ϖ : v.adicCompletion K)‖ ^ m₂)
    (t : GL (Fin 2) (v.adicCompletion K))
    (ht : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![a, b])
    (τ : @Measure (AutomorphicForm.localCentralizer K v t) (AutomorphicForm.localCentralizerBorel K v t))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v t) τ)
    (hτ1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegral K v t τ
      (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * x)) I) :
    ((‖a - b‖ : ℝ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ j * I =
      if m₁ + m₂ = (k : ℤ) + 2 * (j : ℤ) then
        ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff (m₁ - m₂)
      else 0 :=
  P2mSatake.main K v ϖ hϖ hϖ0 n rT hrT z hz k j a b hab m₁ m₂ ha hb t ht τ hτ hτ1 I hI

end S_AutomorphicForm_norm_sub_mul_absNorm_pow_mul_eq_T_add_T_neg_one_pow_apply_of_isOrbitalIntegral_sum_indicator_heckeWord_diagonal
end P2MW
export P2MW.S_AutomorphicForm_norm_sub_mul_absNorm_pow_mul_eq_T_add_T_neg_one_pow_apply_of_isOrbitalIntegral_sum_indicator_heckeWord_diagonal (solution)
