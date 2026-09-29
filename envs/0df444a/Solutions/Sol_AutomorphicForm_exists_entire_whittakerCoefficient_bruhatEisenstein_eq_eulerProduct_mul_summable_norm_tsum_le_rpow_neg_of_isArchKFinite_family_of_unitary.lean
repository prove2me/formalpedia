-- Prove2me | solution 1 for AutomorphicForm.exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/953f0dd2-13e9-5b1a-b4b8-78b37ce6f985

import Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_of_flat_family_of_unitary
import Theorems.Thm_AutomorphicForm_continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn
import Theorems.Thm_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound_of_rpow_inv_le
import Theorems.Thm_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth
import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family
import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq"
p2m_attr_erase "simp" "SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

section EulerSplitBlock
open IsDedekindDomain NumberField AutomorphicForm
open scoped Classical

namespace Ws31
namespace Asm25
namespace Euler

section Generic

variable {ι α : Type*} [CommMonoid α] [TopologicalSpace α] [ContinuousMul α]

theorem hasProd_subtype_not_mem_of_subset (f : ι → α) (S T : Finset ι) (hST : S ⊆ T)
    (hT : Multipliable (fun v : {v : ι // v ∉ T} => f v.1)) :
    HasProd (fun v : {v : ι // v ∉ S} => f v.1) ((∏ v ∈ T \ S, f v) * ∏' v : {v : ι // v ∉ T}, f v.1) := by
  set b : α := ∏' v : {v : ι // v ∉ T}, f v.1 with hbdef
  have hb : HasProd (fun v : {v : ι // v ∉ T} => f v.1) b := hT.hasProd

  set gT : ι → α := fun v => if v ∈ T then 1 else f v with hgT
  have hinjT : Function.Injective (Subtype.val : {v : ι // v ∉ T} → ι) := Subtype.val_injective
  have h1T : ∀ x, x ∉ Set.range (Subtype.val : {v : ι // v ∉ T} → ι) → gT x = 1 := by
    intro x hx
    have hxT : x ∈ T := by
      by_contra h
      exact hx ⟨⟨x, h⟩, rfl⟩
    simp only [hgT, hxT, if_true]
  have hgTb : HasProd gT b := by
    rw [← hinjT.hasProd_iff h1T]
    have e : gT ∘ (Subtype.val : {v : ι // v ∉ T} → ι) = fun v : {v : ι // v ∉ T} => f v.1 := by
      funext v
      simp only [Function.comp_apply, hgT, v.2, if_false]
    rw [e]
    exact hb

  set gF : ι → α := fun v => if v ∈ T \ S then f v else 1 with hgF
  have hgF1 : ∀ v ∉ T \ S, gF v = 1 := fun v hv => by simp only [hgF, hv, if_false]
  have hgFp : HasProd gF (∏ v ∈ T \ S, f v) := by
    have h : HasProd gF (∏ v ∈ T \ S, gF v) := hasProd_prod_of_ne_finset_one hgF1
    have e : ∏ v ∈ T \ S, gF v = ∏ v ∈ T \ S, f v :=
      Finset.prod_congr rfl fun v hv => by simp only [hgF, hv, if_true]
    rw [← e]
    exact h
  have hprod : HasProd (fun v => gF v * gT v) ((∏ v ∈ T \ S, f v) * b) := hgFp.mul hgTb

  have hinjS : Function.Injective (Subtype.val : {v : ι // v ∉ S} → ι) := Subtype.val_injective
  have h1S : ∀ x, x ∉ Set.range (Subtype.val : {v : ι // v ∉ S} → ι) → gF x * gT x = 1 := by
    intro x hx
    have hxS : x ∈ S := by
      by_contra h
      exact hx ⟨⟨x, h⟩, rfl⟩
    have hxT : x ∈ T := hST hxS
    have hxTS : x ∉ T \ S := by simp only [Finset.mem_sdiff, hxS, not_true_eq_false, and_false, not_false_eq_true]
    simp only [hgF, hgT, hxTS, hxT, if_false, if_true, one_mul]
  have h := (hinjS.hasProd_iff h1S).2 hprod
  have e : (fun v => gF v * gT v) ∘ (Subtype.val : {v : ι // v ∉ S} → ι) = fun v : {v : ι // v ∉ S} => f v.1 := by
    funext v
    obtain ⟨v, hv⟩ := v
    simp only [Function.comp_apply]
    by_cases hvT : v ∈ T
    · have : v ∈ T \ S := Finset.mem_sdiff.2 ⟨hvT, hv⟩
      simp only [hgF, hgT, this, hvT, if_true, mul_one]
    · have : v ∉ T \ S := fun h' => hvT (Finset.mem_sdiff.1 h').1
      simp only [hgF, hgT, this, hvT, if_false, one_mul]
  rw [e] at h
  exact h

variable [T2Space α]

theorem tprod_subtype_not_mem_eq_prod_sdiff_mul (f : ι → α) (S T : Finset ι) (hST : S ⊆ T)
    (hT : Multipliable (fun v : {v : ι // v ∉ T} => f v.1)) :
    Multipliable (fun v : {v : ι // v ∉ S} => f v.1) ∧
    ∏' v : {v : ι // v ∉ S}, f v.1 = (∏ v ∈ T \ S, f v) * ∏' v : {v : ι // v ∉ T}, f v.1 :=
  ⟨(hasProd_subtype_not_mem_of_subset f S T hST hT).multipliable,
   (hasProd_subtype_not_mem_of_subset f S T hST hT).tprod_eq⟩

end Generic

section Concrete

variable (F : Type) [Field F] [NumberField F]

theorem norm_localChar_eq_one_of_isUnitaryChar {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hχ : IsUnitaryChar (𝓞 F) F χ) (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    ‖((NumberField.TateGlobal.localChar χ v u : ℂˣ) : ℂ)‖ = 1 :=
  hχ _

theorem hasProd_inv₀ {κ : Type*} {f : κ → ℂ} {a : ℂ} (hf : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  have h : (fun s : Finset κ => ∏ b ∈ s, (f b)⁻¹) = fun s => (∏ b ∈ s, f b)⁻¹ := by
    funext s
    exact Finset.prod_inv_distrib (f := f) (s := s)
  unfold HasProd at hf ⊢
  rw [h]
  exact hf.inv₀ ha

theorem euler_point (S : Finset (HeightOneSpectrum (𝓞 F))) (z : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ)
    (hz : ∀ v, ‖z v‖ ≤ 1) (s' : ℂ) (hs' : 1 < s'.re) :
    Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s'))) ∧
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s')))
      ≠ 0 := by
  obtain ⟨hE1, -, hE3⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S z hz
  obtain ⟨a, ha⟩ := hE1 s' hs'
  have ha0 : a ≠ 0 := by rw [← ha.tprod_eq]; exact hE3 s' hs'
  have hinv := hasProd_inv₀ ha ha0
  simp only [inv_inv] at hinv
  exact ⟨hinv.multipliable, by rw [hinv.tprod_eq]; exact inv_ne_zero ha0⟩

private theorem one_lt_re_two_mul_add_one {s : ℂ} (hs : 0 < s.re) : 1 < (2 * s + 1).re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
    Complex.one_re]
  linarith

theorem eulerBlock_split (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsUnitaryChar (𝓞 F) F χ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (S T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) (s : ℂ) (hs : 0 < s.re) :
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
      = (∏ v ∈ T \ S, (1 - ((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
        * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) *
            ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) := by
  set f : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    1 - ((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))
    with hf
  have hT : Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T} => f v.1) :=
    (euler_point F T (fun v => ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ))
      (fun v => (norm_localChar_eq_one_of_isUnitaryChar F hχ v.1 (ϖ v.1)).le) (2 * s + 1)
      (one_lt_re_two_mul_add_one hs)).1
  exact (tprod_subtype_not_mem_eq_prod_sdiff_mul f S T hST hT).2

theorem eulerBlock_ne_zero (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsUnitaryChar (𝓞 F) F χ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) (hs : 0 < s.re) :
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T},
        (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) ≠ 0 :=
  (euler_point F T (fun v => ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ))
    (fun v => (norm_localChar_eq_one_of_isUnitaryChar F hχ v.1 (ϖ v.1)).le) (2 * s + 1)
    (one_lt_re_two_mul_add_one hs)).2

theorem differentiableOn_eulerBlock (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsUnitaryChar (𝓞 F) F χ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T},
        (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) {s : ℂ | 0 < s.re} := by
  set z : {v : HeightOneSpectrum (𝓞 F) // v ∉ T} → ℂ :=
    fun v => ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) with hz
  have hzle : ∀ v, ‖z v‖ ≤ 1 := fun v => (norm_localChar_eq_one_of_isUnitaryChar F hχ v.1 (ϖ v.1)).le
  obtain ⟨hE1, hE2, hE3⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F T z hzle
  have hD : DifferentiableOn ℂ (fun s' : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T},
      (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s'))) {s' : ℂ | 1 < s'.re} := by
    refine (hE2.inv fun s' hs' => hE3 s' hs').congr fun s' hs' => ?_
    obtain ⟨a, ha⟩ := hE1 s' hs'
    have ha0 : a ≠ 0 := by rw [← ha.tprod_eq]; exact hE3 s' hs'
    have hinv := hasProd_inv₀ ha ha0
    simp only [inv_inv] at hinv
    simp only [Pi.inv_apply]
    rw [hinv.tprod_eq, ha.tprod_eq]
  have haff : DifferentiableOn ℂ (fun s : ℂ => 2 * s + 1) {s : ℂ | 0 < s.re} :=
    ((differentiable_id.const_mul (2 : ℂ)).add_const 1).differentiableOn
  have hmaps : Set.MapsTo (fun s : ℂ => 2 * s + 1) {s : ℂ | 0 < s.re} {s' : ℂ | 1 < s'.re} :=
    fun s hs => one_lt_re_two_mul_add_one hs
  exact (hD.comp haff hmaps)

end Concrete

end Ws31.Asm25.Euler

end EulerSplitBlock

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.InfinitePlace
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain Filter Topology
open scoped NNReal

noncomputable section

namespace Ws31
namespace NctEntire

section Generic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem isInducedSection_finset_sum {ι : Type*} (t : Finset ι) {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    (c : ι → ℂ) (f : ι → AdelicGL2 R K → ℂ) (hf : ∀ i ∈ t, IsInducedSection R K χ₁ χ₂ (f i)) :
    IsInducedSection R K χ₁ χ₂ (fun x => ∑ i ∈ t, c i * f i x) := by
  intro b hb g
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [hf i hi b hb g]
  ring

private theorem apply_unipotentGL2_mul_of_isInducedSection {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ} {f : AdelicGL2 R K → ℂ}
    (hf : IsInducedSection R K χ₁ χ₂ f) (u : AdeleRing R K) (g : AdelicGL2 R K) :
    f (unipotentGL2 u * g) = f g := by
  rw [hf (unipotentGL2 u) (unipotentGL2_mem_borelSubgroup u) g, borelDiagFst_unipotentGL2, borelDiagSnd_unipotentGL2,
    map_one, map_one, Units.val_one, one_mul, one_mul]

private theorem centralScalar_mul_comm (z : (AdeleRing R K)ˣ) (g : AdelicGL2 R K) :
    centralScalar R K z * g = g * centralScalar R K z := by
  apply Units.ext
  change Matrix.scalar (Fin 2) (z : AdeleRing R K) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
    = (g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) * Matrix.scalar (Fin 2) (z : AdeleRing R K)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

end Generic

end Ws31.NctEntire

namespace Ws31
namespace NctEntire

section Eis

variable (F : Type) [Field F] [NumberField F]

private def Eis (f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  f g + ∑' ξ : F, f (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)

private theorem Eis_mul_right (f : AdelicGL2 (𝓞 F) F → ℂ) (g k : AdelicGL2 (𝓞 F) F) :
    Eis F f (g * k) = Eis F (fun x => f (x * k)) g := by
  simp only [Eis, mul_assoc]

private theorem Eis_unipotent_periodic {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsInducedSection (𝓞 F) F χ₁ χ₂ f) (β : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    Eis F f (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = Eis F f (unipotentGL2 u * g) := by
  unfold Eis
  congr 1
  · rw [apply_unipotentGL2_mul_of_isInducedSection hf, apply_unipotentGL2_mul_of_isInducedSection hf]
  · have hterm : ∀ ξ : F,
        f (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) *
          (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g))
        = (fun ζ : F => f (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ζ) *
            (unipotentGL2 u * g))) (ξ + β) := by
      intro ξ
      simp only [map_add, unipotentGL2_add, mul_assoc]
    simp only [hterm]
    exact (Equiv.addRight β).tsum_eq (fun ζ : F => f (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ζ) *
            (unipotentGL2 u * g)))

private theorem Eis_centralScalar_mul {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsInducedSection (𝓞 F) F χ₁ χ₂ f) (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    Eis F f (centralScalar (𝓞 F) F z * g) = (((χ₁ z : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ)) * Eis F f g := by
  have hz : ∀ g' : AdelicGL2 (𝓞 F) F, f (centralScalar (𝓞 F) F z * g')
      = (((χ₁ z : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ)) * f g' := by
    intro g'
    rw [hf _ (centralScalar_mem_adelicBorel (𝓞 F) F z) g', borelDiagFst_centralScalar, borelDiagSnd_centralScalar]
  unfold Eis
  rw [mul_add, ← tsum_mul_left]
  congr 1
  · exact hz g
  · refine tsum_congr (fun ξ => ?_)
    have hc : adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * centralScalar (𝓞 F) F z
        = centralScalar (𝓞 F) F z * (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ)) :=
      (centralScalar_mul_comm z _).symm
    rw [← mul_assoc, hc, mul_assoc, hz]

private theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 F) F : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  change Continuous (Units.map (Matrix.scalar (Fin 2)).toMonoidHom : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F)
  refine Continuous.units_map _ ?_
  change Continuous fun a : AdeleRing (𝓞 F) F => Matrix.scalar (Fin 2) a
  simp only [Matrix.scalar_apply]
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

private theorem Eis_finset_sum {ι : Type*} (t : Finset ι) (c : ι → ℂ) (f : ι → AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hs : ∀ i ∈ t, Summable (fun ξ : F => f i (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))) :
    Eis F (fun x => ∑ i ∈ t, c i * f i x) g = ∑ i ∈ t, c i * Eis F (f i) g := by
  unfold Eis
  rw [Summable.tsum_finsetSum (fun i hi => (hs i hi).mul_left (c i))]
  simp only [mul_add, Finset.sum_add_distrib, tsum_mul_left]

private theorem whittakerCoefficient_centralScalar_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (ξ : F) (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ f ξ (centralScalar (𝓞 F) F z * g)
      = whittakerCoefficient F pins ψ (fun x => f (centralScalar (𝓞 F) F z * x)) ξ g := by
  unfold whittakerCoefficient
  congr 1
  funext u
  congr 2
  rw [← mul_assoc, ← centralScalar_mul_comm z (unipotentGL2 u), mul_assoc]

private theorem whittakerCoefficient_mul_right (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (ξ : F) (g k : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ f ξ (g * k) = whittakerCoefficient F pins ψ (fun x => f (x * k)) ξ g := by
  unfold whittakerCoefficient
  simp only [mul_assoc]

private theorem whittakerCoefficient_const_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (cst : ℂ) (f : AdelicGL2 (𝓞 F) F → ℂ) (ξ : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun x => cst * f x) ξ g = cst * whittakerCoefficient F pins ψ f ξ g := by
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1
  funext u
  ring

private theorem whittakerCoefficient_zero_fun (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ξ : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun _ => (0 : ℂ)) ξ g = 0 := by
  unfold whittakerCoefficient
  simp

end Eis

end Ws31.NctEntire

namespace Ws31
namespace NctEntire

section BorelCoords

variable (F : Type) [Field F] [NumberField F]

private def xB (b : ↥(adelicBorel (𝓞 F) F)) : AdeleRing (𝓞 F) F :=
  ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 * (((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)

private def yB (b : ↥(adelicBorel (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ := borelDiagFst b * (borelDiagSnd b)⁻¹

private theorem scalar_fin_two {A : Type*} [CommRing A] (t : A) : Matrix.scalar (Fin 2) t = !![t, 0; 0, t] := by
  ext i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagonal_fin_two' {A : Type*} [CommRing A] (y : A) : Matrix.diagonal ![y, 1] = !![y, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem matrix_product_aux {A : Type*} [CommRing A] (x t y : A) :
    !![(1 : A), x; 0, 1] * Matrix.scalar (Fin 2) t * Matrix.diagonal ![y, 1] = !![t * y, x * t; 0, t] := by
  rw [scalar_fin_two, diagonal_fin_two', Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem borel_eq_unipotent_mul_central_mul_diagOne (b : ↥(adelicBorel (𝓞 F) F)) :
    (b : AdelicGL2 (𝓞 F) F) = unipotentGL2 (xB F b) * centralScalar (𝓞 F) F (borelDiagSnd b) * diagOne (yB F b) := by
  set t : AdeleRing (𝓞 F) F := ((borelDiagSnd b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) with ht
  set ti : AdeleRing (𝓞 F) F := (((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) with hti
  set a : AdeleRing (𝓞 F) F := ((borelDiagFst b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) with ha
  have h10 : ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := b.2
  have h00 : ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = a := rfl
  have h11 : ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = t := rfl
  have hinv : t * ti = 1 := by rw [ht, hti]; exact Units.mul_inv _
  have hy : ((yB F b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = a * ti := by
    simp only [yB, Units.val_mul, ha, hti]
  have hx : xB F b = ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 * ti := rfl
  apply Units.ext
  change ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    = !![1, xB F b; 0, 1] * Matrix.scalar (Fin 2) t * Matrix.diagonal ![((yB F b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]
  rw [matrix_product_aux, hy, hx]
  ext i j
  fin_cases i <;> fin_cases j
  · change ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = t * (a * ti)
    rw [h00, mul_left_comm, hinv, mul_one]
  · change ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1
      = ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 * ti * t
    rw [mul_assoc, mul_comm ti t, hinv, mul_one]
  · change ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
    exact h10
  · change ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = t
    exact h11

end BorelCoords

end Ws31.NctEntire

namespace Ws31
namespace NctEntire

section Glue

variable (F : Type) [Field F] [NumberField F]

private theorem yB_mul (b b' : ↥(adelicBorel (𝓞 F) F)) : yB F (b * b') = yB F b * yB F b' := by
  simp only [yB, map_mul, mul_inv]
  rw [mul_mul_mul_comm]

private theorem val_apply_yB (χ : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (b : ↥(adelicBorel (𝓞 F) F)) :
    ((χ (yB F b) : ℝˣ) : ℝ) = ((χ (borelDiagFst b) : ℝˣ) : ℝ) / ((χ (borelDiagSnd b) : ℝˣ) : ℝ) := by
  simp only [yB, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]

private theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) := by
  have : (adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F))
      = (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) ⁻¹' {0} := by
    ext g; rfl
  rw [this]
  exact isClosed_singleton.preimage ((Units.continuous_val).matrix_elem 1 0)

private theorem continuous_borel_val :
    Continuous fun b : ↥(adelicBorel (𝓞 F) F) =>
      ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
  Units.continuous_val.comp continuous_subtype_val

private theorem continuous_borel_inv_val :
    Continuous fun b : ↥(adelicBorel (𝓞 F) F) =>
      (((b : AdelicGL2 (𝓞 F) F)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
  Units.continuous_coe_inv.comp continuous_subtype_val

private theorem continuous_borelDiagFst :
    Continuous (borelDiagFst : ↥(adelicBorel (𝓞 F) F) → (AdeleRing (𝓞 F) F)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_borel_val F).matrix_elem 0 0).congr (fun b => rfl)
  · exact ((continuous_borel_inv_val F).matrix_elem 0 0).congr (fun b => rfl)

private theorem continuous_borelDiagSnd :
    Continuous (borelDiagSnd : ↥(adelicBorel (𝓞 F) F) → (AdeleRing (𝓞 F) F)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_borel_val F).matrix_elem 1 1).congr (fun b => rfl)
  · exact ((continuous_borel_inv_val F).matrix_elem 1 1).congr (fun b => rfl)

private theorem continuous_xB : Continuous (xB F) := by
  refine (((continuous_borel_val F).matrix_elem 0 1).mul
    (Units.continuous_coe_inv.comp (continuous_borelDiagSnd F))).congr (fun b => rfl)

private theorem continuous_yB : Continuous (yB F) := by
  refine ((continuous_borelDiagFst F).mul (continuous_borelDiagSnd F).inv).congr (fun b => rfl)

private theorem exists_isCompact_forall_yB_mem (Ω : Set (AdelicGL2 (𝓞 F) F)) (hΩ : IsCompact Ω) :
    ∃ Y : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact Y ∧
      ∀ (b : ↥(adelicBorel (𝓞 F) F)) (k : AdelicGL2 (𝓞 F) F),
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        (b : AdelicGL2 (𝓞 F) F) * k ∈ Ω → yB F b ∈ Y := by
  set Kc : Set (AdelicGL2 (𝓞 F) F) := {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))} with hKc
  have hKc_cpt : IsCompact Kc := isCompact_adelicMaximalCompact F
  set S : Set (AdelicGL2 (𝓞 F) F) := (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => p.1 * p.2⁻¹) '' (Ω ×ˢ Kc)
    with hS
  have hS_cpt : IsCompact S := (hΩ.prod hKc_cpt).image (continuous_fst.mul continuous_snd.inv)
  have hSB : IsCompact ((Subtype.val : ↥(adelicBorel (𝓞 F) F) → AdelicGL2 (𝓞 F) F) ⁻¹' S) :=
    (isClosed_adelicBorel F).isClosedEmbedding_subtypeVal.isCompact_preimage hS_cpt
  refine ⟨yB F '' (Subtype.val ⁻¹' S), hSB.image (continuous_yB F), ?_⟩
  intro b k hk1 hk2 hmem
  refine ⟨b, ?_, rfl⟩
  show (b : AdelicGL2 (𝓞 F) F) ∈ S
  exact ⟨((b : AdelicGL2 (𝓞 F) F) * k, k), ⟨hmem, hk1, hk2⟩, mul_inv_cancel_right _ _⟩

open scoped Classical in

private theorem continuousOn_iwasawaFormula (U : Set ℂ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) (ρc : (AdeleRing (𝓞 F) F)ˣ → ℂ) (hρc : Continuous ρc) (ξ : F)
    (n : ℕ) (m : Fin n → ℕ) (c : Fin n → ℂ → ℂ) (hc : ∀ i, Continuous (c i))
    (a : (i : Fin n) → Fin (m i) → AdelicGL2 (𝓞 F) F → ℂ)
    (ha : ∀ i j, ContinuousOn (a i j) {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})
    (𝒥 : (i : Fin n) → Fin (m i) → ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (h𝒥c : ∀ i j, ContinuousOn (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => 𝒥 i j p.1 p.2)
        (U ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        if hb : p.2.1 ∈ adelicBorel (𝓞 F) F then
          ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ * xB F ⟨p.2.1, hb⟩) * ρc (borelDiagSnd ⟨p.2.1, hb⟩) *
            ∑ i, c i p.1 * ∑ j, a i j p.2.2 * 𝒥 i j p.1 (yB F ⟨p.2.1, hb⟩)
        else 0)
      (U ×ˢ ((adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) ×ˢ
        {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})) := by
  set Kc : Set (AdelicGL2 (𝓞 F) F) := {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))} with hKc
  set B : Set (AdelicGL2 (𝓞 F) F) := (adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) with hB
  set S : Set (ℂ × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F) := U ×ˢ (B ×ˢ Kc) with hS

  let xT : AdelicGL2 (𝓞 F) F → AdeleRing (𝓞 F) F := fun g =>
    if hg : g ∈ adelicBorel (𝓞 F) F then xB F ⟨g, hg⟩ else 0
  let yT : AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ := fun g =>
    if hg : g ∈ adelicBorel (𝓞 F) F then yB F ⟨g, hg⟩ else 1
  let zT : AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ := fun g =>
    if hg : g ∈ adelicBorel (𝓞 F) F then borelDiagSnd ⟨g, hg⟩ else 1
  have hzT : ContinuousOn zT B := by
    rw [continuousOn_iff_continuous_restrict]
    have : B.domRestrict zT = fun b : ↥(adelicBorel (𝓞 F) F) => borelDiagSnd b := by
      funext b
      exact dif_pos b.2
    rw [this]
    exact continuous_borelDiagSnd F
  have hxT : ContinuousOn xT B := by
    rw [continuousOn_iff_continuous_restrict]
    have : B.domRestrict xT = fun b : ↥(adelicBorel (𝓞 F) F) => xB F b := by
      funext b
      exact dif_pos b.2
    rw [this]
    exact continuous_xB F
  have hyT : ContinuousOn yT B := by
    rw [continuousOn_iff_continuous_restrict]
    have : B.domRestrict yT = fun b : ↥(adelicBorel (𝓞 F) F) => yB F b := by
      funext b
      exact dif_pos b.2
    rw [this]
    exact continuous_yB F
  have hπB : ∀ p ∈ S, p.2.1 ∈ B := fun p hp => hp.2.1
  have hπK : ∀ p ∈ S, p.2.2 ∈ Kc := fun p hp => hp.2.2
  have hxS : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => xT p.2.1) S :=
    hxT.comp continuous_snd.fst.continuousOn hπB
  have hyS : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => yT p.2.1) S :=
    hyT.comp continuous_snd.fst.continuousOn hπB
  have hsyS : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => (p.1, yT p.2.1)) S :=
    continuous_fst.continuousOn.prodMk hyS
  have hsy_maps : Set.MapsTo (fun p : ℂ × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => (p.1, yT p.2.1)) S
      (U ×ˢ Set.univ) := fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have hzS : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => zT p.2.1) S :=
    hzT.comp continuous_snd.fst.continuousOn hπB
  have hg : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
      ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ * xT p.2.1) * ρc (zT p.2.1) *
        ∑ i, c i p.1 * ∑ j, a i j p.2.2 * 𝒥 i j p.1 (yT p.2.1)) S := by
    refine ContinuousOn.mul ((hψ.comp_continuousOn (continuousOn_const.mul hxS)).mul (hρc.comp_continuousOn hzS)) ?_
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    refine ((hc i).comp continuous_fst).continuousOn.mul ?_
    refine continuousOn_finsetSum _ (fun j _ => ?_)
    exact ((ha i j).comp continuous_snd.snd.continuousOn hπK).mul ((h𝒥c i j).comp hsyS hsy_maps)
  refine hg.congr (fun p hp => ?_)
  have hb : p.2.1 ∈ adelicBorel (𝓞 F) F := hp.2.1
  simp only [xT, yT, zT, dif_pos hb]

open scoped Classical in

private theorem exists_summable_majorant
    (n : ℕ) (m : Fin n → ℕ) (c : Fin n → ℂ → ℂ) (hc : ∀ i, Continuous (c i))
    (a : (i : Fin n) → Fin (m i) → AdelicGL2 (𝓞 F) F → ℂ)
    (ha : ∀ i j, ContinuousOn (a i j) {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})
    (𝒥 : (i : Fin n) → Fin (m i) → {ξ : F // ξ ≠ 0} → ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (h𝒥d : ∀ i j, ∀ (C : Set ℂ) (U : Set (AdeleRing (𝓞 F) F)ˣ) (r₀ : ℝ), IsCompact C → IsCompact U → 0 < r₀ →
        ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), ∀ N : ℕ, ∃ c : ℝ,
          ∀ s ∈ C, ∀ u ∈ U, ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), r₀ ≤ r →
            (z : AdeleRing (𝓞 F) F).2 = 1 →
            (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
            ∀ ξ : {ξ : F // ξ ≠ 0},
              ((ξ : F) ∉ I → 𝒥 i j ξ s (z * u) = 0) ∧
              ‖𝒥 i j ξ s (z * u)‖ ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) *
                (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
                ∏ w : {w : InfinitePlace F // w.IsComplex},
                  (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ)))
    (C : Set ℂ) (Y : Set (AdeleRing (𝓞 F) F)ˣ) (hC : IsCompact C)
    (hY : IsCompact Y) :
    ∃ u : {ξ : F // ξ ≠ 0} → ℝ, Summable u ∧
      ∀ (ξ : {ξ : F // ξ ≠ 0}), ∀ s ∈ C, ∀ k : AdelicGL2 (𝓞 F) F,
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        ∀ y ∈ Y, ‖∑ i, c i s * ∑ j, a i j k * 𝒥 i j ξ s y‖ ≤ u ξ := by
  set Kc : Set (AdelicGL2 (𝓞 F) F) := {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))} with hKc
  have hKc_cpt : IsCompact Kc := isCompact_adelicMaximalCompact F

  have hcb : ∀ i, ∃ Mc : ℝ, 0 ≤ Mc ∧ ∀ s ∈ C, ‖c i s‖ ≤ Mc := by
    intro i
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hc i).continuousOn
    exact ⟨max M 0, le_max_right _ _, fun s hs => (hM s hs).trans (le_max_left _ _)⟩
  choose Mc hMc0 hMc using hcb
  have hab : ∀ i j, ∃ Ma : ℝ, 0 ≤ Ma ∧ ∀ k ∈ Kc, ‖a i j k‖ ≤ Ma := by
    intro i j
    obtain ⟨M, hM⟩ := hKc_cpt.exists_bound_of_continuousOn (ha i j)
    exact ⟨max M 0, le_max_right _ _, fun k hk => (hM k hk).trans (le_max_left _ _)⟩
  choose Ma hMa0 hMa using hab

  choose kk II hd using fun i j => h𝒥d i j C Y 1 hC hY one_pos
  choose N₀ hN₀ using fun i j =>
    NumberField.mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg F (II i j) (kk i j) 0 1 one_pos
  choose cc hcc using fun i j => hd i j (N₀ i j)
  choose Cst hCst using fun i j => hN₀ i j (N₀ i j) le_rfl

  let wt : (i : Fin n) → Fin (m i) → F → ℝ := fun i j ξ =>
    (max 1 ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ^ kk i j *
      (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + 1 * |(mixedEmbedding F ξ).1 w|) ^ (-(N₀ i j : ℝ))) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + 1 * ‖(mixedEmbedding F ξ).2 w‖) ^ (-(2 * N₀ i j : ℝ))
  have hwt0 : ∀ i j ξ, 0 ≤ wt i j ξ := by
    intro i j ξ
    simp only [wt]
    positivity
  let g : (i : Fin n) → Fin (m i) → {ξ : F // ξ ≠ 0} → ℝ := fun i j ξ =>
    if (ξ : F) ∈ II i j then wt i j ξ else 0
  have hg0 : ∀ i j ξ, 0 ≤ g i j ξ := by
    intro i j ξ
    simp only [g]
    split_ifs
    · exact hwt0 i j ξ
    · exact le_rfl

  have hg_summ : ∀ i j, Summable (g i j) := by
    intro i j
    obtain ⟨hS, -⟩ := hCst i j 1 le_rfl
    let ι : {ξ : F // ξ ≠ 0 ∧ ξ ∈ II i j} → {ξ : F // ξ ≠ 0} := fun ξ => ⟨ξ.1, ξ.2.1⟩
    have hι : Function.Injective ι := by
      intro x y h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
    have hsupp : ∀ x, x ∉ Set.range ι → g i j x = 0 := by
      intro x hx
      simp only [g]
      rw [if_neg]
      intro hxI
      exact hx ⟨⟨x.1, x.2, hxI⟩, rfl⟩
    refine (hι.summable_iff hsupp).mp ?_
    have hcomp : g i j ∘ ι = fun ξ => wt i j ξ.1 := by
      funext ξ
      simp only [Function.comp_apply, g, ι, if_pos ξ.2.2]
    rw [hcomp]
    exact hS

  have hJ : ∀ i j (ξ : {ξ : F // ξ ≠ 0}), ∀ s ∈ C, ∀ y ∈ Y, ‖𝒥 i j ξ s y‖ ≤ max (cc i j) 0 * g i j ξ := by
    intro i j ξ s hs y hy
    have h1 : ((1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl
    have h2 : ∀ w : InfinitePlace F,
        Completion.extensionEmbedding w (((1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w) = ((1 : ℝ) : ℂ) := by
      intro w
      rw [Complex.ofReal_one]
      exact map_one (Completion.extensionEmbedding w)
    obtain ⟨hzero, hbd⟩ := hcc i j s hs y hy 1 1 le_rfl h1 h2 ξ
    rw [one_mul] at hzero hbd
    by_cases hξ : (ξ : F) ∈ II i j
    · have hg : g i j ξ = wt i j ξ := if_pos hξ
      rw [hg]
      calc ‖𝒥 i j ξ s y‖ ≤ _ := hbd
        _ = cc i j * wt i j ξ := by
          simp only [wt, Real.one_rpow]
          ring
        _ ≤ max (cc i j) 0 * wt i j ξ := mul_le_mul_of_nonneg_right (le_max_left _ _) (hwt0 i j ξ)
    · rw [hzero hξ, norm_zero]
      exact mul_nonneg (le_max_right _ _) (hg0 i j ξ)
  refine ⟨fun ξ => ∑ i, Mc i * ∑ j, Ma i j * (max (cc i j) 0 * g i j ξ), ?_, ?_⟩
  · refine summable_sum (fun i _ => ?_)
    refine Summable.mul_left (Mc i) ?_
    refine summable_sum (fun j _ => ?_)
    exact ((hg_summ i j).mul_left _).mul_left _
  · intro ξ s hs k hk1 hk2 y hy
    have hk : k ∈ Kc := ⟨hk1, hk2⟩
    calc ‖∑ i, c i s * ∑ j, a i j k * 𝒥 i j ξ s y‖
        ≤ ∑ i, ‖c i s * ∑ j, a i j k * 𝒥 i j ξ s y‖ := norm_sum_le _ _
      _ ≤ ∑ i, Mc i * ∑ j, Ma i j * (max (cc i j) 0 * g i j ξ) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [norm_mul]
        refine mul_le_mul (hMc i s hs) ?_ (norm_nonneg _) (hMc0 i)
        calc ‖∑ j, a i j k * 𝒥 i j ξ s y‖ ≤ ∑ j, ‖a i j k * 𝒥 i j ξ s y‖ := norm_sum_le _ _
          _ ≤ ∑ j, Ma i j * (max (cc i j) 0 * g i j ξ) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            rw [norm_mul]
            exact mul_le_mul (hMa i j k hk) (hJ i j ξ s hs y hy) (norm_nonneg _) (hMa0 i j)

open scoped Classical in

private theorem exists_tsum_norm_le_mul_rpow_neg
    (n : ℕ) (m : Fin n → ℕ) (c : Fin n → ℂ → ℂ) (hc : ∀ i, Continuous (c i))
    (a : (i : Fin n) → Fin (m i) → AdelicGL2 (𝓞 F) F → ℂ)
    (ha : ∀ i j, ContinuousOn (a i j) {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})
    (𝒥 : (i : Fin n) → Fin (m i) → {ξ : F // ξ ≠ 0} → ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (h𝒥e : ∀ i j (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ),
        𝒥 i j ξ s (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
          = 𝒥 i j ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ s y)
    (h𝒥d : ∀ i j, ∀ (C : Set ℂ) (U : Set (AdeleRing (𝓞 F) F)ˣ) (r₀ : ℝ), IsCompact C → IsCompact U → 0 < r₀ →
        ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), ∀ N : ℕ, ∃ c : ℝ,
          ∀ s ∈ C, ∀ u ∈ U, ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), r₀ ≤ r →
            (z : AdeleRing (𝓞 F) F).2 = 1 →
            (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
            ∀ ξ : {ξ : F // ξ ≠ 0},
              ((ξ : F) ∉ I → 𝒥 i j ξ s (z * u) = 0) ∧
              ‖𝒥 i j ξ s (z * u)‖ ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) *
                (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
                ∏ w : {w : InfinitePlace F // w.IsComplex},
                  (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ)))
    (C : Set ℂ) (Y : Set (AdeleRing (𝓞 F) F)ˣ) (c' : ℝ) (N : ℕ) (hC : IsCompact C)
    (hY : IsCompact Y) (hc' : 0 < c') :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∃ M : ℝ, ∀ s ∈ C, ∀ k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      ∀ y₀ ∈ Y, ∀ y₁ : (AdeleRing (𝓞 F) F)ˣ, c' ≤ ((α y₁ : ℝˣ) : ℝ) →
        Summable (fun ξ : {ξ : F // ξ ≠ 0} => ‖∑ i, c i s * ∑ j, a i j k * 𝒥 i j ξ s (y₁ * y₀)‖) ∧
        ∑' ξ : {ξ : F // ξ ≠ 0}, ‖∑ i, c i s * ∑ j, a i j k * 𝒥 i j ξ s (y₁ * y₀)‖
          ≤ M * ((α y₁ : ℝˣ) : ℝ) ^ (-(N : ℝ)) := by
  intro α

  obtain ⟨U', hU'c, hL⟩ :=
    (NumberField.exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound_of_rpow_inv_le F) Y hY

  have hd0 := fun i j => h𝒥d i j C U' (c' ^ ((Module.finrank ℚ F : ℝ)⁻¹)) hC hU'c (Real.rpow_pos_of_pos hc' _)
  choose kk II hd1 using hd0
  choose cc hd using hd1

  obtain ⟨σ₁, hσ₁⟩ := (hC.image Complex.continuous_re).bddBelow
  obtain ⟨σ₂, hσ₂⟩ := (hC.image Complex.continuous_re).bddAbove

  have hL1 := fun i j => hL (kk i j) (II i j) σ₁ σ₂ c' N hc'
  choose Nd MM hM using hL1

  have hcb := fun i => hC.exists_bound_of_continuousOn (hc i).continuousOn
  choose Mc hMc using hcb
  have hKc : IsCompact {k : AdelicGL2 (𝓞 F) F | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
      ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))} :=
    isCompact_adelicMaximalCompact F
  have hab := fun i j => hKc.exists_bound_of_continuousOn (ha i j)
  choose Ma hMa using hab
  refine ⟨∑ i, max (Mc i) 0 * ∑ j, max (Ma i j) 0 * MM i j (cc i j (Nd i j)), ?_⟩
  intro s hs k hk1 hk2 y₀ hy₀ y₁ hy₁
  have hσs1 : σ₁ ≤ s.re := hσ₁ (Set.mem_image_of_mem _ hs)
  have hσs2 : s.re ≤ σ₂ := hσ₂ (Set.mem_image_of_mem _ hs)

  have hij : ∀ i j, Summable (fun ξ : {ξ : F // ξ ≠ 0} => ‖𝒥 i j ξ s (y₁ * y₀)‖) ∧
      ∑' ξ : {ξ : F // ξ ≠ 0}, ‖𝒥 i j ξ s (y₁ * y₀)‖
        ≤ MM i j (cc i j (Nd i j)) * ((α y₁ : ℝˣ) : ℝ) ^ (-(N : ℝ)) := by
    intro i j
    refine hM i j (cc i j (Nd i j)) (fun ξ y => ‖𝒥 i j ξ s y‖) s.re hσs1 hσs2 (fun _ _ => norm_nonneg _)
      (fun ξ η y => congrArg norm (h𝒥e i j ξ η s y)) ?_ y₁ y₀ hy₀ hy₁
    intro u hu z r hr hz2 hz1 ξ
    obtain ⟨h1, h2⟩ := hd i j (Nd i j) s hs u hu z r hr hz2 hz1 ξ
    exact ⟨fun h => by beta_reduce; rw [h1 h, norm_zero], h2⟩

  have hbd : ∀ ξ : {ξ : F // ξ ≠ 0}, ‖∑ i, c i s * ∑ j, a i j k * 𝒥 i j ξ s (y₁ * y₀)‖ ≤
      ∑ i, max (Mc i) 0 * ∑ j, max (Ma i j) 0 * ‖𝒥 i j ξ s (y₁ * y₀)‖ := by
    intro ξ
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    refine mul_le_mul ((hMc i s hs).trans (le_max_left _ _)) ?_ (norm_nonneg _) (le_max_right _ _)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((hMa i j k ⟨hk1, hk2⟩).trans (le_max_left _ _)) (norm_nonneg _)

  have hBsum : HasSum (fun ξ : {ξ : F // ξ ≠ 0} => ∑ i, max (Mc i) 0 * ∑ j, max (Ma i j) 0 * ‖𝒥 i j ξ s (y₁ * y₀)‖)
      (∑ i, max (Mc i) 0 * ∑ j, max (Ma i j) 0 * ∑' ξ : {ξ : F // ξ ≠ 0}, ‖𝒥 i j ξ s (y₁ * y₀)‖) :=
    hasSum_sum fun i _ => HasSum.mul_left _ (hasSum_sum fun j _ => HasSum.mul_left _ (hij i j).1.hasSum)
  have hSum : Summable (fun ξ : {ξ : F // ξ ≠ 0} => ‖∑ i, c i s * ∑ j, a i j k * 𝒥 i j ξ s (y₁ * y₀)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd hBsum.summable
  refine ⟨hSum, ?_⟩
  calc ∑' ξ : {ξ : F // ξ ≠ 0}, ‖∑ i, c i s * ∑ j, a i j k * 𝒥 i j ξ s (y₁ * y₀)‖
      ≤ ∑' ξ : {ξ : F // ξ ≠ 0}, ∑ i, max (Mc i) 0 * ∑ j, max (Ma i j) 0 * ‖𝒥 i j ξ s (y₁ * y₀)‖ :=
        hSum.tsum_le_tsum hbd hBsum.summable
    _ = ∑ i, max (Mc i) 0 * ∑ j, max (Ma i j) 0 * ∑' ξ : {ξ : F // ξ ≠ 0}, ‖𝒥 i j ξ s (y₁ * y₀)‖ := hBsum.tsum_eq
    _ ≤ ∑ i, max (Mc i) 0 * ∑ j, max (Ma i j) 0 * (MM i j (cc i j (Nd i j)) * ((α y₁ : ℝˣ) : ℝ) ^ (-(N : ℝ))) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hij i j).2 (le_max_right _ _)
    _ = (∑ i, max (Mc i) 0 * ∑ j, max (Ma i j) 0 * MM i j (cc i j (Nd i j))) * ((α y₁ : ℝˣ) : ℝ) ^ (-(N : ℝ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, Finset.sum_mul]
        refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
        ring

private theorem isUnitaryChar_mul_inv {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) : IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) := by
  intro x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
    hμ x, hν x, inv_one, mul_one]

open scoped Classical in

private theorem dilationBound_mul (f : ℂ → ℂ) (hf : Continuous f)
    (𝒥 : {ξ : F // ξ ≠ 0} → ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (h𝒥d : ∀ (C : Set ℂ) (U : Set (AdeleRing (𝓞 F) F)ˣ) (r₀ : ℝ), IsCompact C → IsCompact U → 0 < r₀ →
        ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), ∀ N : ℕ, ∃ c : ℝ,
          ∀ s ∈ C, ∀ u ∈ U, ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), r₀ ≤ r →
            (z : AdeleRing (𝓞 F) F).2 = 1 →
            (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
            ∀ ξ : {ξ : F // ξ ≠ 0},
              ((ξ : F) ∉ I → 𝒥 ξ s (z * u) = 0) ∧
              ‖𝒥 ξ s (z * u)‖ ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) *
                (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
                ∏ w : {w : InfinitePlace F // w.IsComplex},
                  (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ))) :
    ∀ (C : Set ℂ) (U : Set (AdeleRing (𝓞 F) F)ˣ) (r₀ : ℝ), IsCompact C → IsCompact U → 0 < r₀ →
        ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), ∀ N : ℕ, ∃ c : ℝ,
          ∀ s ∈ C, ∀ u ∈ U, ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), r₀ ≤ r →
            (z : AdeleRing (𝓞 F) F).2 = 1 →
            (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
            ∀ ξ : {ξ : F // ξ ≠ 0},
              ((ξ : F) ∉ I → f s * 𝒥 ξ s (z * u) = 0) ∧
              ‖f s * 𝒥 ξ s (z * u)‖ ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) *
                (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
                ∏ w : {w : InfinitePlace F // w.IsComplex},
                  (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ)) := by
  intro C U r₀ hC hU hr₀
  obtain ⟨k, I, hN⟩ := h𝒥d C U r₀ hC hU hr₀
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨k, I, fun N => ?_⟩
  obtain ⟨c, hc⟩ := hN N
  refine ⟨max B 0 * max c 0, fun s hs u hu z r hr hz2 hz1 ξ => ?_⟩
  obtain ⟨h0, hbd⟩ := hc s hs u hu z r hr hz2 hz1 ξ
  refine ⟨fun hξ => by rw [h0 hξ, mul_zero], ?_⟩
  have hr0 : 0 < r := hr₀.trans_le hr
  set W : ℝ := r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) *
      (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
      (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ)) with hW
  have hW0 : 0 ≤ W := by
    simp only [hW]
    positivity
  have hbd' : ‖𝒥 ξ s (z * u)‖ ≤ max c 0 * W := by
    have : c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) *
        (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
        (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ))
        = c * W := by simp only [hW]; ring
    rw [this] at hbd
    exact hbd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW0)
  rw [norm_mul]
  calc ‖f s‖ * ‖𝒥 ξ s (z * u)‖ ≤ max B 0 * (max c 0 * W) :=
        mul_le_mul ((hB s hs).trans (le_max_left _ _)) hbd' (norm_nonneg _) (le_max_right _ _)
    _ = max B 0 * max c 0 * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) *
      (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
      (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ)) := by
        simp only [hW]; ring

end Glue

end Ws31.NctEntire

namespace Ws31
namespace NctEntire

section Main

variable (F : Type) [Field F] [NumberField F]

private def IsK (k : AdelicGL2 (𝓞 F) F) : Prop :=
  glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
    ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))

private theorem isK_mul {k k' : AdelicGL2 (𝓞 F) F} (hk : IsK F k) (hk' : IsK F k') : IsK F (k * k') := by
  refine ⟨?_, fun w => ?_⟩
  · rw [map_mul]; exact (finiteIntegralGL2 (𝓞 F) F).mul_mem hk.1 hk'.1
  · rw [map_mul, map_mul]; exact (hk.2 w).mul (hk'.2 w)

private theorem eq_of_isInducedSection_of_eqOn_K {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {f f' : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsInducedSection (𝓞 F) F χ₁ χ₂ f) (hf' : IsInducedSection (𝓞 F) F χ₁ χ₂ f')
    (h : ∀ k, IsK F k → f k = f' k) : f = f' := by
  funext g
  obtain ⟨b, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  rw [hf b hb k, hf' b hb k, h k ⟨hk1, hk2⟩]

private theorem main :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (𝒱 : {ξ : F // ξ ≠ 0} → ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (h : AdelicGL2 (𝓞 F) F), Differentiable ℂ (fun s => 𝒱 ξ s h)) ∧
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 < s.re →
        whittakerCoefficient F (productionPins F) ψ (E s) (ξ : F) h
          = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * 𝒱 ξ s h) ∧
      (∀ ξ : {ξ : F // ξ ≠ 0}, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => 𝒱 ξ p.1 p.2)) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)), IsCompact C → IsCompact Ω →
        ∃ u : {ξ : F // ξ ≠ 0} → ℝ, Summable u ∧
          ∀ (ξ : {ξ : F // ξ ≠ 0}), ∀ s ∈ C, ∀ h ∈ Ω, ‖𝒱 ξ s h‖ ≤ u ξ) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
        IsCompact C → IsCompact Ω → 0 < c' →
        ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
          ω ∈ Ω → c' ≤ hgt b →
            Summable (fun ξ : {ξ : F // ξ ≠ 0} => ‖𝒱 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖) ∧
            ∑' ξ : {ξ : F // ξ ≠ 0}, ‖𝒱 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤ M * (hgt b) ^ (-(N : ℝ))) := by
  intro α hα μ ν hμ hν hμF hνF ψ hψ φ hφ hφK hφf hφjc hφhol ϖ hϖ
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  classical

  by_cases hφ0 : ∀ s g, φ s g = 0
  · intro E hgt
    have hE : ∀ s, E s = fun _ => (0 : ℂ) := by
      intro s
      funext h
      show φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h) = 0
      simp [hφ0]
    refine ⟨∅, fun _ _ _ => 0, ?_, ?_, ?_, ?_, ?_⟩
    · intro ξ h
      exact differentiable_const 0
    · intro ξ s h hs
      rw [hE s, whittakerCoefficient_zero_fun, mul_zero]
    · intro ξ
      exact continuous_const
    · intro C Ω hC hΩ
      exact ⟨fun _ => 0, summable_zero, fun ξ s hs h hh => by simp⟩
    · intro C Ω c' N hC hΩ hc'
      refine ⟨0, fun s hs b ω hω hb => ⟨?_, ?_⟩⟩
      · simpa using (summable_zero : Summable (fun _ : {ξ : F // ξ ≠ 0} => (0 : ℝ)))
      · simp
  push Not at hφ0
  obtain ⟨s₀, g₀, hne⟩ := hφ0

  obtain ⟨n, c, ψf, hc, hψf, hψfK, hψff, hψfjc, hψfhol, hψfflat, hφsum⟩ :=
    AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family F hα μ ν φ hφ hφK hφf hφjc hφhol

  have hψc0 : ∀ i, Continuous (ψf i 0) := fun i => (hψfjc i).comp (Continuous.prodMk_right 0)
  choose m e a he ha hexp using fun i =>
    AutomorphicForm.exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth F (ψf i 0)
      (hψfK i 0) (hψff i 0) (hψc0 i)
  have hind_e : ∀ i j, IsInducedSection (𝓞 F) F (etaFst μ α hα 0) (etaSnd ν α hα 0) (e i j) := by
    intro i j
    obtain ⟨nn, cc, kk, _hkk, heq⟩ := (he i j).1
    rw [heq]
    exact isInducedSection_finset_sum Finset.univ cc (fun l x => ψf i 0 (x * kk l))
      (fun l _ => (hψf i 0).rightTranslate (kk l))
  have hcont_e : ∀ i j, Continuous (e i j) := by
    intro i j
    obtain ⟨nn, cc, kk, _hkk, heq⟩ := (he i j).1
    rw [heq]
    exact continuous_finsetSum _ (fun l _ => continuous_const.mul ((hψc0 i).comp (continuous_mul_const _)))

  choose E hE0 hEind hEK hEf hEjc hEhol hEflat using fun i j =>
    AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection F hα μ ν 0 (e i j)
      (hind_e i j) (he i j).2.1 (he i j).2.2 (hcont_e i j)

  have hexpand : ∀ i (s : ℂ) (k : AdelicGL2 (𝓞 F) F), IsK F k →
      (fun x => ψf i s (x * k)) = fun x => ∑ j, a i j k * E i j s x := by
    intro i s k hk
    refine eq_of_isInducedSection_of_eqOn_K F ((hψf i s).rightTranslate k)
      (isInducedSection_finset_sum Finset.univ (fun j => a i j k) (fun j => E i j s) (fun j _ => hEind i j s)) ?_
    intro k' hk'
    have h1 : ψf i s (k' * k) = ψf i 0 (k' * k) :=
      hψfflat i s 0 (k' * k) (isK_mul F hk' hk).1 (isK_mul F hk' hk).2
    show ψf i s (k' * k) = ∑ j, a i j k * E i j s k'
    rw [h1, hexp i k hk.1 hk.2 k']
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hE0 i j, hEflat i j 0 s k' hk'.1 hk'.2]

  choose 𝒥₀ h𝒥₀a h𝒥₀S h𝒥₀c h𝒥₀e h𝒥₀d using fun i j =>
    AutomorphicForm.exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_of_flat_family_of_unitary F hα μ ν
      hμ hν hμF hνF ψ hψ (E i j) (hEind i j) (hEK i j) (hEf i j) (hEjc i j) (hEhol i j) (hEflat i j) ϖ hϖ
  choose Sf hSf using h𝒥₀S

  let S : Finset (HeightOneSpectrum (𝓞 F)) :=
    (Finset.univ : Finset ((i : Fin n) × Fin (m i))).biUnion (fun p => Sf p.1 p.2)
  have hSfS : ∀ i j, Sf i j ⊆ S := fun i j =>
    Finset.subset_biUnion_of_mem (fun p : (i : Fin n) × Fin (m i) => Sf p.1 p.2) (Finset.mem_univ (⟨i, j⟩ : (i : Fin n) × Fin (m i)))
  have hχu : IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) := isUnitaryChar_mul_inv F hμ hν
  let ef : HeightOneSpectrum (𝓞 F) → ℂ → ℂ := fun v s =>
    1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v (ϖ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))
  let Fc : (i : Fin n) → Fin (m i) → ℂ → ℂ := fun i j s => ∏ v ∈ S \ Sf i j, ef v s
  let P : ℂ → ℂ := fun s => ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, ef v.1 s
  have hef : ∀ v, Differentiable ℂ (ef v) := by
    intro v s
    have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
    simp only [ef]
    exact (differentiableAt_const _).sub ((differentiableAt_const _).mul
      ((((differentiableAt_id.const_mul (2 : ℂ)).add_const 1).neg).const_cpow (Or.inl hN)))
  have hFc : ∀ i j, Differentiable ℂ (Fc i j) := by
    intro i j
    simp only [Fc]
    exact Differentiable.fun_finsetProd (fun v _ => hef v)
  have hPne : ∀ s : ℂ, 1 < s.re → P s ≠ 0 := fun s hs =>
    Ws31.Asm25.Euler.eulerBlock_ne_zero F (μ * ν⁻¹) hχu ϖ S s (by linarith)
  have hsplit : ∀ i j (s : ℂ), 1 < s.re →
      (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf i j}, ef v.1 s) = Fc i j s * P s := fun i j s hs =>
    Ws31.Asm25.Euler.eulerBlock_split F (μ * ν⁻¹) hχu ϖ (Sf i j) S (hSfS i j) s (by linarith)
  let 𝒥 : (i : Fin n) → Fin (m i) → {ξ : F // ξ ≠ 0} → ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ :=
    fun i j ξ s y => Fc i j s * 𝒥₀ i j ξ s y
  have h𝒥a : ∀ i j (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ), Differentiable ℂ (fun s => 𝒥 i j ξ s y) :=
    fun i j ξ y => (hFc i j).mul (differentiableOn_univ.1 (h𝒥₀a i j ξ y).differentiableOn)
  have h𝒥b : ∀ i j (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ), 1 < s.re →
      P s * 𝒥 i j ξ s y = whittakerCoefficient F (productionPins F) ψ (Eis F (E i j s)) (ξ : F) (diagOne y) := by
    intro i j ξ s y hs
    have h := hSf i j ξ s y hs
    change whittakerCoefficient F (productionPins F) ψ (Eis F (E i j s)) (ξ : F) (diagOne y)
      = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf i j}, ef v.1 s) * 𝒥₀ i j ξ s y at h
    rw [h, hsplit i j s hs]
    simp only [𝒥]
    ring
  have h𝒥c : ∀ i j (ξ : {ξ : F // ξ ≠ 0}), Continuous (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => 𝒥 i j ξ p.1 p.2) :=
    fun i j ξ => ((hFc i j).continuous.comp continuous_fst).mul (h𝒥₀c i j ξ)
  have h𝒥e : ∀ i j (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ),
      𝒥 i j ξ s (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
        = 𝒥 i j ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ s y := by
    intro i j ξ η s y
    simp only [𝒥, h𝒥₀e]
  have h𝒥d := fun i j => dilationBound_mul F (Fc i j) (hFc i j).continuous (𝒥₀ i j) (h𝒥₀d i j)

  choose bI kI hbI hkI1 hkI2 hdecI using fun g : AdelicGL2 (𝓞 F) F => AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  let χc : (AdeleRing (𝓞 F) F)ˣ → ℂ := fun z => ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ)
  have hcentral : ∀ (s : ℂ) (z : (AdeleRing (𝓞 F) F)ˣ),
      ((etaFst μ α hα s z : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ) = χc z := by
    intro s z
    rw [← Units.val_mul, etaFst_mul_etaSnd, Units.val_mul]

  have hχc : Continuous χc := by
    have hval : ∀ z, χc z = φ s₀ (centralScalar (𝓞 F) F z * g₀) / φ s₀ g₀ := by
      intro z
      rw [(hφ s₀) _ (centralScalar_mem_adelicBorel (𝓞 F) F z) g₀, borelDiagFst_centralScalar,
        borelDiagSnd_centralScalar, hcentral s₀ z, mul_div_assoc, div_self hne, mul_one]
    rw [show χc = fun z => φ s₀ (centralScalar (𝓞 F) F z * g₀) / φ s₀ g₀ from funext hval]
    exact (hφjc.comp (continuous_const.prodMk ((continuous_centralScalar F).mul continuous_const))).div_const _
  let Φ : {ξ : F // ξ ≠ 0} → ℂ → ↥(adelicBorel (𝓞 F) F) → AdelicGL2 (𝓞 F) F → ℂ := fun ξ s b k =>
    ψ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * xB F b) * χc (borelDiagSnd b) *
      ∑ i, c i s * ∑ j, a i j k * 𝒥 i j ξ s (yB F b)
  let Φ' : {ξ : F // ξ ≠ 0} → ℂ → ↥(adelicBorel (𝓞 F) F) → AdelicGL2 (𝓞 F) F → ℂ := fun ξ s b k =>
    ψ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * xB F b) * χc (borelDiagSnd b) *
      ∑ i, c i s * ∑ j, a i j k * (P s * 𝒥 i j ξ s (yB F b))
  have hΦP : ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (b : ↥(adelicBorel (𝓞 F) F)) (k : AdelicGL2 (𝓞 F) F),
      Φ' ξ s b k = P s * Φ ξ s b k := by
    intro ξ s b k
    simp only [Φ, Φ', mul_assoc, Finset.mul_sum, mul_left_comm _ (P s)]
  let 𝒲 : {ξ : F // ξ ≠ 0} → ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun ξ s h => Φ ξ s ⟨bI h, hbI h⟩ (kI h)

  have hW : ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), 1 < s.re → ∀ (b : ↥(adelicBorel (𝓞 F) F)) (k : AdelicGL2 (𝓞 F) F), IsK F k →
      whittakerCoefficient F (productionPins F) ψ (Eis F (φ s)) (ξ : F) ((b : AdelicGL2 (𝓞 F) F) * k) = Φ' ξ s b k := by
    intro ξ s hs b k hk
    have hs' : 1 / 2 < s.re := by linarith

    rw [whittakerCoefficient_mul_right]
    have hEk : (fun x => Eis F (φ s) (x * k)) = Eis F (fun x => φ s (x * k)) := by
      funext x; exact Eis_mul_right F (φ s) x k
    rw [hEk]

    have hRk : (fun x => φ s (x * k)) = fun x => ∑ i, c i s * ∑ j, a i j k * E i j s x := by
      funext x
      rw [hφsum s (x * k)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have := congrFun (hexpand i s k hk) x
      beta_reduce at this
      rw [this]
    have hRind : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (fun x => φ s (x * k)) :=
      (hφ s).rightTranslate k

    rw [borel_eq_unipotent_mul_central_mul_diagOne F b, mul_assoc]
    unfold productionPins
    rw [AutomorphicForm.whittakerCoefficient_unipotentGL2_mul F _ _ _ ψ hψ.principalInvariant _ _
      (fun β u => Eis_unipotent_periodic F hRind β u _)]
    rw [whittakerCoefficient_centralScalar_mul]
    have hEz : (fun x => Eis F (fun x => φ s (x * k)) (centralScalar (𝓞 F) F (borelDiagSnd b) * x))
        = fun x => χc (borelDiagSnd b) * Eis F (fun x => φ s (x * k)) x := by
      funext x
      rw [Eis_centralScalar_mul F hRind, hcentral s]
    rw [hEz, whittakerCoefficient_const_mul, hRk]

    have hsumm : ∀ i j (g : AdelicGL2 (𝓞 F) F), Summable (fun ξ' : F =>
        E i j s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g)) := by
      intro i j g
      exact (AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hα μ ν hμ
        hν s hs' (E i j s) (hEind i j s) ((hEjc i j).comp (Continuous.prodMk_right s)) g).of_norm
    have hEisLin : Eis F (fun x => ∑ i, c i s * ∑ j, a i j k * E i j s x)
        = fun x => ∑ i, c i s * ∑ j, a i j k * Eis F (E i j s) x := by
      funext x
      have hinner : ∀ i, Summable (fun ξ' : F => (fun y => ∑ j, a i j k * E i j s y)
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * x)) := by
        intro i
        exact summable_sum (fun j _ => (hsumm i j x).mul_left (a i j k))
      rw [Eis_finset_sum F Finset.univ (fun i => c i s) (fun i y => ∑ j, a i j k * E i j s y) x (fun i _ => hinner i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Eis_finset_sum F Finset.univ (fun j => a i j k) (fun j => E i j s) x (fun j _ => hsumm i j x)]
    rw [hEisLin]
    have hEc : ∀ i j, Continuous (Eis F (E i j s)) := by
      intro i j
      exact ((hEjc i j).comp (Continuous.prodMk_right s)).add
        (AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half F hα μ ν hμ hν
          s hs' (E i j s) (hEind i j s) ((hEjc i j).comp (Continuous.prodMk_right s)))
    rw [AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous F _ _ _ ψ hψ.continuous n
      (fun i y => ∑ j, a i j k * Eis F (E i j s) y) (fun i => continuous_finsetSum _ (fun j _ => continuous_const.mul (hEc i j)))
      (fun i => c i s)]
    rw [← mul_assoc]
    simp only [Φ']
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous F _ _ _ ψ hψ.continuous (m i)
      (fun j => Eis F (E i j s)) (fun j => hEc i j) (fun j => a i j k)]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hb' := h𝒥b i j ξ s (yB F b) hs
    unfold productionPins at hb'
    rw [hb']

  have hΦan : ∀ (ξ : {ξ : F // ξ ≠ 0}) (b : ↥(adelicBorel (𝓞 F) F)) (k : AdelicGL2 (𝓞 F) F),
      AnalyticOnNhd ℂ (fun s => Φ ξ s b k) Set.univ := by
    intro ξ b k s _
    simp only [Φ]
    refine analyticAt_const.mul ?_
    refine Finset.analyticAt_fun_sum _ (fun i _ => ?_)
    refine ((hc i).analyticAt s).mul ?_
    refine Finset.analyticAt_fun_sum _ (fun j _ => ?_)
    exact analyticAt_const.mul ((h𝒥a i j ξ (yB F b)).analyticAt s)
  have hwd : ∀ (ξ : {ξ : F // ξ ≠ 0}) (b b' : ↥(adelicBorel (𝓞 F) F)) (k k' : AdelicGL2 (𝓞 F) F),
      IsK F k → IsK F k' → (b : AdelicGL2 (𝓞 F) F) * k = (b' : AdelicGL2 (𝓞 F) F) * k' →
      ∀ s : ℂ, Φ ξ s b k = Φ ξ s b' k' := by
    intro ξ b b' k k' hk hk' hbk s
    have hev : (fun s => Φ ξ s b k) =ᶠ[𝓝 (2 : ℂ)] fun s => Φ ξ s b' k' := by
      have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      have h2' : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
        show (1 : ℝ) < (2 : ℂ).re
        norm_num
      filter_upwards [hopen.mem_nhds h2'] with t ht
      have e1 := hW ξ t ht b k hk
      have e2 := hW ξ t ht b' k' hk'
      rw [hbk] at e1
      rw [hΦP] at e1 e2
      exact mul_left_cancel₀ (hPne t ht) (e1.symm.trans e2)
    exact (hΦan ξ b k).eqOn_of_preconnected_of_eventuallyEq (hΦan ξ b' k') isPreconnected_univ
      (Set.mem_univ (2 : ℂ)) hev (Set.mem_univ s)
  have hψ1 : ∀ x, ‖ψ x‖ = 1 := NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ
  have hχc1 : ∀ z, ‖χc z‖ = 1 := by
    intro z
    simp only [χc, norm_mul, hμ z, hν z, mul_one]
  have hnormΦ : ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (b : ↥(adelicBorel (𝓞 F) F)) (k : AdelicGL2 (𝓞 F) F),
      ‖Φ ξ s b k‖ = ‖∑ i, c i s * ∑ j, a i j k * 𝒥 i j ξ s (yB F b)‖ := by
    intro ξ s b k
    simp only [Φ, norm_mul, hψ1, hχc1, one_mul]
  intro E hgt
  refine ⟨S, 𝒲, ?_, ?_, ?_, ?_, ?_⟩

  · intro ξ h
    exact differentiableOn_univ.1 (hΦan ξ ⟨bI h, hbI h⟩ (kI h)).differentiableOn

  · intro ξ s h hs
    show whittakerCoefficient F (productionPins F) ψ (Eis F (φ s)) (ξ : F) h = P s * Φ ξ s ⟨bI h, hbI h⟩ (kI h)
    conv_lhs => rw [hdecI h]
    rw [← hΦP]
    exact hW ξ s hs ⟨bI h, hbI h⟩ (kI h) ⟨hkI1 h, hkI2 h⟩

  · intro ξ
    have hco := AutomorphicForm.continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn F (Set.univ : Set ℂ) isOpen_univ
      (fun s h => 𝒲 ξ s h)
      (fun s g k => if hg : g ∈ adelicBorel (𝓞 F) F then Φ ξ s ⟨g, hg⟩ k else 0) ?_ ?_
    · rw [Set.univ_prod_univ, continuousOn_univ] at hco
      exact hco
    · exact continuousOn_iwasawaFormula F Set.univ ψ hψ.continuous χc hχc (ξ : F) n m c (fun i => (hc i).continuous) a ha
        (fun i j => 𝒥 i j ξ) (fun i j => (h𝒥c i j ξ).continuousOn)
    · intro s _ g hg k hk1 hk2
      have h := hwd ξ ⟨bI (g * k), hbI (g * k)⟩ ⟨g, hg⟩ (kI (g * k)) k ⟨hkI1 (g * k), hkI2 (g * k)⟩ ⟨hk1, hk2⟩
        (hdecI (g * k)).symm s
      show 𝒲 ξ s (g * k) = (if hg : g ∈ adelicBorel (𝓞 F) F then Φ ξ s ⟨g, hg⟩ k else 0)
      rw [dif_pos hg]
      exact h

  · intro C Ω hC hΩ
    obtain ⟨Y, hY, hYmem⟩ := exists_isCompact_forall_yB_mem F Ω hΩ
    obtain ⟨u, hu, hbound⟩ := exists_summable_majorant F n m c (fun i => (hc i).continuous) a ha 𝒥 h𝒥d
      C Y hC hY
    refine ⟨u, hu, fun ξ s hs h hh => ?_⟩
    show ‖Φ ξ s ⟨bI h, hbI h⟩ (kI h)‖ ≤ u ξ
    rw [hnormΦ]
    exact hbound ξ s hs (kI h) (hkI1 h) (hkI2 h) _
      (hYmem ⟨bI h, hbI h⟩ (kI h) (hkI1 h) (hkI2 h) (by rw [← hdecI h]; exact hh))

  · intro C Ω c' N hC hΩ hc'
    obtain ⟨Y, hY, hYmem⟩ := exists_isCompact_forall_yB_mem F Ω hΩ
    obtain ⟨M, hM⟩ := exists_tsum_norm_le_mul_rpow_neg F n m c (fun i => (hc i).continuous) a ha 𝒥 h𝒥e h𝒥d
      C Y c' N hC hY hc'
    refine ⟨M, fun s hs b ω hω hb => ?_⟩
    have hkω : IsK F (kI ω) := ⟨hkI1 ω, hkI2 ω⟩
    have hprod : ((b * ⟨bI ω, hbI ω⟩ : ↥(adelicBorel (𝓞 F) F)) : AdelicGL2 (𝓞 F) F) * kI ω
        = (b : AdelicGL2 (𝓞 F) F) * ω := by
      rw [Subgroup.coe_mul, mul_assoc, ← hdecI ω]
    have key : ∀ ξ : {ξ : F // ξ ≠ 0},
        𝒲 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω) = Φ ξ s (b * ⟨bI ω, hbI ω⟩) (kI ω) := by
      intro ξ
      show Φ ξ s ⟨bI ((b : AdelicGL2 (𝓞 F) F) * ω), hbI _⟩ (kI ((b : AdelicGL2 (𝓞 F) F) * ω)) = _
      exact hwd ξ _ _ _ _ ⟨hkI1 _, hkI2 _⟩ hkω (by rw [← hdecI, hprod]) s
    have hnorm : (fun ξ : {ξ : F // ξ ≠ 0} => ‖𝒲 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖)
        = fun ξ => ‖∑ i, c i s * ∑ j, a i j (kI ω) * 𝒥 i j ξ s (yB F b * yB F ⟨bI ω, hbI ω⟩)‖ := by
      funext ξ
      rw [key, hnormΦ, yB_mul]
    have hhgt : hgt b = ((α (yB F b) : ℝˣ) : ℝ) := (val_apply_yB F α b).symm
    rw [hnorm, hhgt]
    rw [hhgt] at hb
    exact hM s hs (kI ω) (hkI1 ω) (hkI2 ω) (yB F ⟨bI ω, hbI ω⟩)
      (hYmem ⟨bI ω, hbI ω⟩ (kI ω) (hkI1 ω) (hkI2 ω) (by rw [← hdecI ω]; exact hω)) (yB F b) hb

end Main

end Ws31.NctEntire

end

p2m_open "MeasureTheory NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace AutomorphicForm"
open AutomorphicForm.WindowedSiegel Filter Topology IsDedekindDomain
open scoped NNReal

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (𝒱 : {ξ : F // ξ ≠ 0} → ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (h : AdelicGL2 (𝓞 F) F), Differentiable ℂ (fun s => 𝒱 ξ s h)) ∧
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 < s.re →
        whittakerCoefficient F (productionPins F) ψ (E s) (ξ : F) h
          = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * 𝒱 ξ s h) ∧
      (∀ ξ : {ξ : F // ξ ≠ 0}, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => 𝒱 ξ p.1 p.2)) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)), IsCompact C → IsCompact Ω →
        ∃ u : {ξ : F // ξ ≠ 0} → ℝ, Summable u ∧
          ∀ (ξ : {ξ : F // ξ ≠ 0}), ∀ s ∈ C, ∀ h ∈ Ω, ‖𝒱 ξ s h‖ ≤ u ξ) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
        IsCompact C → IsCompact Ω → 0 < c' →
        ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
          ω ∈ Ω → c' ≤ hgt b →
            Summable (fun ξ : {ξ : F // ξ ≠ 0} => ‖𝒱 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖) ∧
            ∑' ξ : {ξ : F // ξ ≠ 0}, ‖𝒱 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤ M * (hgt b) ^ (-(N : ℝ))) :=
  Ws31.NctEntire.main F

end S_AutomorphicForm_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
end P2MW
export P2MW.S_AutomorphicForm_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary (solution)
