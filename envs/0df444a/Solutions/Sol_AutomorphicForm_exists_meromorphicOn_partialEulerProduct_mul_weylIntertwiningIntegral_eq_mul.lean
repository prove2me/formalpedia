-- Prove2me | solution 1 for AutomorphicForm.exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/65b3d422-50e0-530b-9194-a9d929e2d4ac

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_EisensteinGeneral_FactorizationDatum
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_exists_localComponents_of_isGlobalAddChar
import Theorems.Thm_EisensteinGeneral_Piece_continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_EisensteinGeneral_Piece_exists_forall_nonempty_factorizationDatum
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_EisensteinGeneral_Piece_integral_smul_add_mul_addChar_neg_mul_eq
import Theorems.Thm_EisensteinGeneral_Glue_integrable_mul_of_integrable_of_integrable
import Theorems.Thm_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod
import Theorems.Thm_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq
import Theorems.Thm_EisensteinGeneral_LocalRam_integrable_twisted_smooth
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply"
p2m_attr_erase "simp" "IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal
set_option autoImplicit false

namespace KIntP7

open Complex

private def Good (f : ℂ → ℂ) : Prop := MeromorphicOn f Set.univ ∧ DifferentiableOn ℂ f {s : ℂ | 0 < s.re}

private theorem good_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Good f :=
  ⟨(hf.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn, hf.differentiableOn⟩

private theorem good_const (c : ℂ) : Good fun _ => c :=
  good_of_differentiable (differentiable_const c)

private theorem good_add {f g : ℂ → ℂ} (hf : Good f) (hg : Good g) : Good fun s => f s + g s :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

private theorem good_mul {f g : ℂ → ℂ} (hf : Good f) (hg : Good g) : Good fun s => f s * g s :=
  ⟨hf.1.mul hg.1, hf.2.mul hg.2⟩

private theorem good_finset_sum {ι : Type} (t : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ t, Good (f i)) :
    Good fun s => ∑ i ∈ t, f i s := by
  classical
  revert hf
  refine Finset.induction_on t ?_ ?_
  · intro _
    simpa using good_const (0 : ℂ)
  · intro a u ha ih hf'
    have hrw : (fun s => ∑ i ∈ insert a u, f i s) = fun s => f a s + ∑ i ∈ u, f i s :=
      funext fun s => Finset.sum_insert ha
    rw [hrw]
    exact good_add (hf' a (Finset.mem_insert_self a u)) (ih fun i hi => hf' i (Finset.mem_insert_of_mem hi))

private theorem good_finset_prod {ι : Type} (t : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ t, Good (f i)) :
    Good fun s => ∏ i ∈ t, f i s := by
  classical
  revert hf
  refine Finset.induction_on t ?_ ?_
  · intro _
    simpa using good_const (1 : ℂ)
  · intro a u ha ih hf'
    have hrw : (fun s => ∏ i ∈ insert a u, f i s) = fun s => f a s * ∏ i ∈ u, f i s :=
      funext fun s => Finset.prod_insert ha
    rw [hrw]
    exact good_mul (hf' a (Finset.mem_insert_self a u)) (ih fun i hi => hf' i (Finset.mem_insert_of_mem hi))

private theorem good_inv_of_entire {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hne : ∀ s : ℂ, 0 < s.re → g s ≠ 0) :
    Good fun s => (g s)⁻¹ :=
  ⟨(good_of_differentiable hg).1.inv, hg.differentiableOn.inv fun s hs => hne s hs⟩

private theorem differentiable_cpow_neg_two_mul_add_one {N : ℝ} (hN : 0 < N) (n : ℕ) :
    Differentiable ℂ fun s : ℂ => (((N : ℂ)) ^ (-(2 * s + 1))) ^ n := by
  have hbase : Differentiable ℂ fun s : ℂ => (N : ℂ) ^ (-(2 * s + 1)) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hN.ne'))
  exact hbase.pow n

private theorem norm_cpow_neg_two_mul_lt_one {N : ℝ} (hN : 2 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    ‖(N : ℂ) ^ (-(2 * s))‖ < 1 := by
  have hNpos : (0 : ℝ) < N := by linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  have hre : (-(2 * s)).re = -(2 * s.re) := by simp
  rw [hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)

private theorem good_tail {a : ℂ} (ha : ‖a‖ = 1) {N : ℝ} (hN : 2 ≤ N) (m : ℕ) :
    Good fun s : ℂ => (a * (N : ℂ) ^ (-(2 * s))) ^ m * (1 - a * (N : ℂ) ^ (-(2 * s)))⁻¹ := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hcp : Differentiable ℂ fun s : ℂ => (N : ℂ) ^ (-(2 * s)) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hNpos.ne'))
  have hnum : Good fun s : ℂ => (a * (N : ℂ) ^ (-(2 * s))) ^ m :=
    good_of_differentiable ((hcp.const_mul a).pow m)
  have hden : Differentiable ℂ fun s : ℂ => 1 - a * (N : ℂ) ^ (-(2 * s)) :=
    (differentiable_const (1 : ℂ)).sub (hcp.const_mul a)
  have hne : ∀ s : ℂ, 0 < s.re → (1 - a * (N : ℂ) ^ (-(2 * s))) ≠ 0 := by
    intro s hs h0
    have h1 : a * (N : ℂ) ^ (-(2 * s)) = 1 := (sub_eq_zero.mp h0).symm
    have h2 : ‖a * (N : ℂ) ^ (-(2 * s))‖ < 1 := by
      rw [norm_mul, ha, one_mul]
      exact norm_cpow_neg_two_mul_lt_one hN hs
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  exact good_mul hnum (good_inv_of_entire hden hne)

private theorem good_Gammaℝ_affine (τ : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Good fun s : ℂ => Gammaℝ (2 * (s + τ * I / 2) + c) := by
  have hinv : Differentiable ℂ fun s : ℂ => (Gammaℝ (2 * (s + τ * I / 2) + c))⁻¹ :=
    differentiable_Gammaℝ_inv.comp (by fun_prop)
  have hne : ∀ s : ℂ, 0 < s.re → (Gammaℝ (2 * (s + τ * I / 2) + c))⁻¹ ≠ 0 := by
    intro s hs
    apply inv_ne_zero
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [add_re, mul_re, ofReal_re, ofReal_im, re_ofNat, im_ofNat, div_ofNat_re, I_re, I_im]
    simp
    linarith
  have h := good_inv_of_entire hinv hne
  simpa only [inv_inv] using h

private theorem good_entire_inv_affine (τ : ℝ) (c : ℂ) :
    Good fun s : ℂ => (Gammaℝ (2 * (s + τ * I / 2) + c))⁻¹ :=
  good_of_differentiable (differentiable_Gammaℝ_inv.comp (by fun_prop))

private theorem good_real_place (k : ℤ) (τ : ℝ) :
    Good fun s : ℂ => (-I) ^ k * (Gammaℝ (2 * (s + τ * I / 2)) * Gammaℝ (2 * (s + τ * I / 2) + 1))
      / (Gammaℝ (2 * (s + τ * I / 2) + 1 + k) * Gammaℝ (2 * (s + τ * I / 2) + 1 - k)) := by
  have h0 : Good fun s : ℂ => Gammaℝ (2 * (s + τ * I / 2) + ((0 : ℝ) : ℂ)) := good_Gammaℝ_affine τ le_rfl
  have h1 : Good fun s : ℂ => Gammaℝ (2 * (s + τ * I / 2) + ((1 : ℝ) : ℂ)) := good_Gammaℝ_affine τ zero_le_one
  have h2 : Good fun s : ℂ => (Gammaℝ (2 * (s + τ * I / 2) + (1 + (k : ℂ))))⁻¹ := good_entire_inv_affine τ _
  have h3 : Good fun s : ℂ => (Gammaℝ (2 * (s + τ * I / 2) + (1 - (k : ℂ))))⁻¹ := good_entire_inv_affine τ _
  simp only [ofReal_zero, add_zero, ofReal_one] at h0 h1
  have hP := good_mul (good_mul (good_mul (good_mul (good_const ((-I) ^ k)) h0) h1) h2) h3
  convert hP using 1
  funext s
  simp only [← add_assoc, ← add_sub_assoc]
  ring

private theorem good_complex_place (a m : ℕ) (ham : a + a ≤ m) (τ : ℝ) :
    Good fun s : ℂ => (Real.pi : ℂ) * (a.factorial : ℂ)
      * Gamma ((2 * s + 1 + (m : ℂ) / 2 + τ * I / 2) - 1 - a) / Gamma (2 * s + 1 + (m : ℂ) / 2 + τ * I / 2) := by

  have hnum_inv : Differentiable ℂ fun s : ℂ => (Gamma ((2 * s + 1 + (m : ℂ) / 2 + τ * I / 2) - 1 - a))⁻¹ :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hnum_ne : ∀ s : ℂ, 0 < s.re → (Gamma ((2 * s + 1 + (m : ℂ) / 2 + τ * I / 2) - 1 - a))⁻¹ ≠ 0 := by
    intro s hs
    apply inv_ne_zero
    apply Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [sub_re, add_re, mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im, natCast_re, one_re,
      div_ofNat_re, neg_re, I_re, I_im] at hre
    simp at hre
    have hm : (a : ℝ) + a ≤ m := by exact_mod_cast ham
    linarith
  have hnum : Good fun s : ℂ => Gamma ((2 * s + 1 + (m : ℂ) / 2 + τ * I / 2) - 1 - a) := by
    simpa only [inv_inv] using good_inv_of_entire hnum_inv hnum_ne
  have hden : Good fun s : ℂ => (Gamma (2 * s + 1 + (m : ℂ) / 2 + τ * I / 2))⁻¹ :=
    good_of_differentiable (differentiable_one_div_Gamma.comp (by fun_prop))
  have hP := good_mul (good_mul (good_const ((Real.pi : ℂ) * (a.factorial : ℂ))) hnum) hden
  convert hP using 1
  rfl

end KIntP7

namespace KIntC

open AutomorphicForm

section
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

private theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

private theorem norm_coeff_lt_one (a : ℂ) (ha : ‖a‖ = 1) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ)
    (hs : 0 < s.re) : ‖a * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 := by
  have h2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm F v
  rw [norm_mul, ha, one_mul,
    Complex.norm_natCast_cpow_of_pos (by have := two_le_absNorm F v; omega) (-(2 * s))]
  have hre : (-(2 * s)).re = -(2 * s.re) := by simp
  rw [hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)

private theorem finprod_eq_prod_mul_finprod_subtype {ι M : Type*} [CommMonoid M] (T : Finset ι)
    (f : ι → M) (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ i, f i = (∏ i ∈ T, f i) * ∏ᶠ i : {i // i ∉ T}, f i.1 := by
  rw [← finprod_mem_univ, ← Set.union_compl_self (↑T : Set ι),
    finprod_mem_union' disjoint_compl_right (hf.subset Set.inter_subset_right)
      (hf.subset Set.inter_subset_right),
    finprod_mem_coe_finset]
  congr 1
  rw [← finprod_set_coe_eq_finprod_mem]
  rfl

variable {F}
variable {ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ}
    {nψ : HeightOneSpectrum (𝓞 F) → ℤ} {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ}
    {Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {g : AdelicGL2 (𝓞 F) F} {S : Finset (HeightOneSpectrum (𝓞 F))}

private theorem h_eq_one (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S) (j : Fin D.n)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) (s : ℂ)
    (y : v.adicCompletion F) (hy : y ∈ v.adicCompletionIntegers F) : D.h j v s y = 1 := by
  have hy' : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hy
  rw [D.hoff j v hv s y]
  simp [hy']

private theorem mulSupport_h_finite (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S) (j : Fin D.n)
    (s : ℂ) (x : AdeleRing (𝓞 F) F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => D.h j v s (x.2 v)).Finite := by
  have hfin :
      {v : HeightOneSpectrum (𝓞 F) | x.2 v ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))}.Finite :=
    Filter.eventually_cofinite.1 x.2.2
  refine (S.finite_toSet.union hfin).subset fun v hv => ?_
  by_contra hv'
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hv'
  exact hv (h_eq_one D j v hv'.1 s (x.2 v) hv'.2)

private theorem finprod_h_eq (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S) (j : Fin D.n) (s : ℂ)
    (x : AdeleRing (𝓞 F) F) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)
      = (∏ v ∈ S, D.h j v s (x.2 v))
        * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            ((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x.2 v.1)
          + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v.1)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x.2 v.1)) := by
  rw [finprod_eq_prod_mul_finprod_subtype S _ (mulSupport_h_finite D j s x)]
  congr 1
  exact finprod_congr fun v => D.hoff j v.1 v.2 s (x.2 v.1)

private theorem integrableOn_A
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μv v).IsAddHaarMeasure]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S)
    (j : Fin D.n) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) :
    IntegrableOn (D.A j v) (v.adicCompletionIntegers F : Set (v.adicCompletion F)) (μv v) := by
  have hO : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers F) from inferInstance)
  refine ContinuousOn.integrableOn_compact hO ?_
  intro x hx
  set r0 : v.adicCompletion F := (ϖ v : v.adicCompletion F) ^ D.mS with hr0
  have hvr0 : Valued.v r0 = Multiplicative.ofAdd (-(D.mS : ℤ)) := by
    rw [hr0, map_pow, hϖ v, ← WithZero.coe_pow, ← ofAdd_nsmul, smul_neg, nsmul_eq_mul, mul_one]
  have hr0v : Valued.v r0 ≠ 0 := by rw [hvr0]; exact WithZero.coe_ne_zero
  have hball : IsOpen {y : v.adicCompletion F | Valued.v y ≤ Valued.v r0} := by
    have hr : Valued.v.restrict r0 ≠ 0 := fun h0 => hr0v ((Valuation.restrict_eq_zero_iff Valued.v).1 h0)
    have hset : {y : v.adicCompletion F | Valued.v y ≤ Valued.v r0}
        = {y | Valued.v.restrict y ≤ Valued.v.restrict r0} :=
      Set.ext fun y => (Valuation.restrict_le_iff Valued.v (x := y) (y := r0)).symm
    rw [hset]
    exact (Valued.isClopen_closedBall (v.adicCompletion F) hr).isOpen
  have hU : {y : v.adicCompletion F | Valued.v (y - x) ≤ Valued.v r0} ∈ nhds x :=
    (hball.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  refine (continuousWithinAt_const (b := D.A j v x)).congr_of_eventuallyEq ?_ rfl
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with y hy hyO
  exact D.hA j v hv x hx y hyO (by rw [← hvr0]; exact hy)

private theorem integrable_h
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μv v).IsAddHaarMeasure]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S)
    (j : Fin D.n) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) (hs : 0 < s.re) : Integrable (D.h j v s) (μv v) := by
  have hlt := norm_coeff_lt_one F _ (D.hχϖ v) v s hs
  by_cases hv : v ∈ S
  · have hI := EisensteinGeneral.LocalRam.integrable_twisted_smooth F v (μv v) (ϖ v) (hϖ v)
      (NumberField.TateGlobal.localChar χ v) (D.cS v) (D.hcS v hv) (D.hχc v hv) D.mS D.hmS (D.A j v)
      (integrableOn_A μv hϖ D j v hv) (D.B j v) (D.hB j v hv) s hlt 1 0 (fun _ _ => AddChar.one_apply _) 0
    have heq : D.h j v s = fun x =>
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (D.A j v) (x)
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * D.B j v y⁻¹) (x))
          * (1 : AddChar (v.adicCompletion F) ℂ) (-(0 * x)) := by
      funext x; rw [AddChar.one_apply, mul_one]; exact D.hon j v hv s x
    rw [heq]; exact hI
  · have hI := (EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq F v (μv v) (ϖ v) (hϖ v)
      (NumberField.TateGlobal.localChar χ v) (D.hχS v hv) s hlt 1 0 (fun _ _ => AddChar.one_apply _) 0).1
    have heq : D.h j v s = fun x =>
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x)
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x))
          * (1 : AddChar (v.adicCompletion F) ℂ) (-(0 * x)) := by
      funext x; rw [AddChar.one_apply, mul_one]; exact D.hoff j v hv s x
    rw [heq]; exact hI

private theorem term_nonneg_le
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μv v).IsAddHaarMeasure]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S)
    (j : Fin D.n) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) (s : ℂ) (hs : 1 / 2 < s.re) :
    0 ≤ ((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
          * (∫ y, ‖D.h j v s y‖ ∂(μv v)) - 1 ∧
      ((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
          * (∫ y, ‖D.h j v s y‖ ∂(μv v)) - 1
        ≤ (1 - (2 : ℝ) ^ (-(2 * s.re)))⁻¹ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) := by
    have hs0 : 0 < s.re := by linarith
    have hq0 : (2 : ℝ) ^ (-(2 * s.re)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hlt := norm_coeff_lt_one F _ (D.hχϖ v) v s hs0
    have hval := (EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq F v (μv v) (ϖ v) (hϖ v)
      (NumberField.TateGlobal.localChar χ v) (D.hχS v hv) s hlt 1 0 (fun _ _ => AddChar.one_apply _) 0).2
    have heq : (fun y => ‖D.h j v s y‖) = fun x =>
        ‖((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x)
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x))
          * (1 : AddChar (v.adicCompletion F) ℂ) (-(0 * x))‖ := by
      funext x; rw [AddChar.one_apply, mul_one, D.hoff j v hv s x]
    have hN2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm F v
    have hN1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
    have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
    have hqq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) ≤ (2 : ℝ) ^ (-(2 * s.re)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hN2 (by linarith)
    have hp0 : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)) := Real.rpow_nonneg (by linarith) _
    have hpq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1))
        ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hOopen : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      (Fact.out : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) v
    have hOcpt : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers F) from inferInstance)
    have hvol : 0 < (μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      ENNReal.toReal_pos ((hOopen.measure_pos (μv v) ⟨0, zero_mem _⟩).ne') hOcpt.measure_lt_top.ne
    rw [D.hχϖ v, one_mul, one_mul] at hval
    have hI : ∫ y, ‖D.h j v s y‖ ∂(μv v)
        = (μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F))
          * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)))
          * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)))⁻¹ := by
      rw [heq]; exact hval
    have hB : (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))) ≠ 0 := by linarith
    have hterm : ((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
          * (∫ y, ‖D.h j v s y‖ ∂(μv v)) - 1
        = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))
            - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)))
          / (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))) := by
      rw [hI]
      field_simp
      ring
    refine ⟨?_, ?_⟩
    · rw [hterm]
      exact div_nonneg (by linarith) (by linarith)
    rw [hterm, div_eq_mul_inv, mul_comm]

    have h1 : (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)))⁻¹ ≤ (1 - (2 : ℝ) ^ (-(2 * s.re)))⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    calc (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)))⁻¹
          * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))
              - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)))
        ≤ (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)))⁻¹
          * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) :=
          mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 (by linarith))
      _ ≤ (1 - (2 : ℝ) ^ (-(2 * s.re)))⁻¹ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by linarith) _)

private theorem summable_h
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μv v).IsAddHaarMeasure]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S)
    (j : Fin D.n) (s : ℂ) (hs : 1 / 2 < s.re) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      ((μv v.1).real (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)))⁻¹
          * (∫ y, ‖D.h j v.1 s y‖ ∂(μv v.1)) - 1 := by
  have hmaj : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      (1 - (2 : ℝ) ^ (-(2 * s.re)))⁻¹ * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) :=
    ((NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt F
      (σ := 2 * s.re) (by linarith)).subtype {v | v ∉ S}).mul_left _
  exact Summable.of_nonneg_of_le (fun v => (term_nonneg_le μv hϖ D j v.1 v.2 s hs).1)
    (fun v => (term_nonneg_le μv hϖ D j v.1 v.2 s hs).2) hmaj

private noncomputable def placeVal
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S)
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) (j : Fin D.n) (v : HeightOneSpectrum (𝓞 F))
    (s : ℂ) : ℂ :=
  ((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
    * ((∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), D.A j v x ∂(μv v))
        + (∑ n ∈ Finset.Ico 1 D.mS,
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ n
              * ∫ x in {x : v.adicCompletion F | Valued.v x = Multiplicative.ofAdd (n : ℤ)},
                  LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ x * D.B j v x⁻¹ ∂(μv v))
        + D.B j v 0 * (∫ u in {u : v.adicCompletion F | Valued.v u = 1},
              LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ u ∂(μv v))
            * (((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) ^ D.mS
            * (1 - ((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹)

private theorem good_placeVal
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S)
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) (j : Fin D.n)
    (v : HeightOneSpectrum (𝓞 F)) : KIntP7.Good (placeVal D μv j v) := by
  have hN : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm F v
  have hN0 : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
  have hT := KIntP7.good_tail (D.hχϖ v) hN D.mS
  have hP : ∀ n : ℕ, KIntP7.Good fun s : ℂ => ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) ^ (-(2 * s + 1))) ^ n :=
    fun n => KIntP7.good_of_differentiable (KIntP7.differentiable_cpow_neg_two_mul_add_one hN0 n)
  simp only [Complex.ofReal_natCast] at hT hP
  have hG := KIntP7.good_mul
    (KIntP7.good_const (((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹))
    (KIntP7.good_add
      (KIntP7.good_add
        (KIntP7.good_const (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), D.A j v x ∂(μv v)))
        (KIntP7.good_finset_sum (Finset.Ico 1 D.mS) (f := fun n s =>
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ n
              * ∫ x in {x : v.adicCompletion F | Valued.v x = Multiplicative.ofAdd (n : ℤ)},
                  LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ x * D.B j v x⁻¹ ∂(μv v))
          fun n _ => KIntP7.good_mul (hP n) (KIntP7.good_const _)))
      (KIntP7.good_mul (KIntP7.good_const (D.B j v 0 * (∫ u in {u : v.adicCompletion F | Valued.v u = 1},
              LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ u ∂(μv v)))) hT))
  unfold placeVal
  convert hG using 1
  funext s
  ring

private theorem inv_vol_mul_integral_h_eq
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μv v).IsAddHaarMeasure]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S)
    (j : Fin D.n) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) (s : ℂ) (hs : 0 < s.re) :
    ((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹ * ∫ y, D.h j v s y ∂(μv v)
      = placeVal D μv j v s := by
  have heq : (fun y => D.h j v s y) = fun x =>
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (D.A j v) (x)
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * D.B j v y⁻¹) (x)) :=
    funext fun x => D.hon j v hv s x
  unfold placeVal
  rw [heq, AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion F v (μv v) (ϖ v) (hϖ v)
    (NumberField.TateGlobal.localChar χ v) ⟨D.cS v, D.hχc v hv⟩ D.mS D.hmS (D.A j v)
    (integrableOn_A μv hϖ D j v hv) (D.B j v)
    (D.hB j v hv) s (norm_coeff_lt_one F _ (D.hχϖ v) v s hs)]

private theorem norm_sub_I (x : ℝ) : ‖(x : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg ((x : ℂ) - Complex.I)), Complex.sq_norm, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.ofReal_im,
    Complex.I_im, zero_sub]
  ring

private theorem norm_unit (x : ℝ) :
    ‖((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)‖ = 1 := by
  have hpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [norm_div, norm_sub_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_self hpos.ne']

private theorem unit_ne_zero (x : ℝ) : ((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 := by
  intro h
  have h1 := norm_unit x
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

private theorem integrable_Wr (k : ℤ) (τ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x : ℝ => (((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2))) := by
  have hmaj : Integrable (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * s.re + 1) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (by rw [Module.finrank_self]; push_cast; linarith)
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (Continuous.mul ?_ ?_).aestronglyMeasurable
    · exact Continuous.zpow₀ (Continuous.div (by fun_prop) (by fun_prop)
        (fun x => Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne')) k
        (fun x => Or.inl (unit_ne_zero x))
    · exact Continuous.cpow (by fun_prop) continuous_const
        (fun x => Complex.ofReal_mem_slitPlane.2 (by positivity))
  · have hre : (-(s + 1 / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2)).re = -(2 * s.re + 1) / 2 := by
      simp [Complex.div_ofNat_re]; ring
    have heq : ‖(((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2))‖
          = ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * s.re + 1) / 2) := by
      rw [norm_mul, norm_zpow, norm_unit x, one_zpow, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre, Real.norm_eq_abs, sq_abs]
    exact heq.le

private theorem integrable_Wc (a b m : ℕ) (habm : a + b ≤ m) (τ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun z : ℂ => z ^ a * (starRingEnd ℂ) z ^ b
      * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + (m : ℂ) / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2))) := by
  have hmaj : Integrable (fun z : ℂ => ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * s.re + 1)) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
      (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · refine ((Continuous.mul (by fun_prop) (by fun_prop)).mul ?_).aestronglyMeasurable
    exact Continuous.cpow (by fun_prop) continuous_const (fun z => Complex.ofReal_mem_slitPlane.2 (by positivity))
  · have hB1 : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    have hBpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by linarith
    have hre : (-(2 * s + 1 + (m : ℂ) / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2)).re
        = -(2 * s.re + 1 + (m : ℝ) / 2) := by
      simp [Complex.div_ofNat_re]
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
      Complex.norm_cpow_eq_rpow_re_of_pos hBpos, hre]
    have hz : ‖z‖ ≤ (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := by
      calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
        _ ≤ Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have hzab : ‖z‖ ^ a * ‖z‖ ^ b ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
      calc ‖z‖ ^ a * ‖z‖ ^ b = ‖z‖ ^ (a + b) := (pow_add _ _ _).symm
        _ ≤ ((1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ (a + b) := pow_le_pow_left₀ (norm_nonneg z) hz _
        _ = (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2 * ((a + b : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]
        _ ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
            refine Real.rpow_le_rpow_of_exponent_le hB1 ?_
            have hm : ((a + b : ℕ) : ℝ) ≤ m := by exact_mod_cast habm
            linarith
    calc ‖z‖ ^ a * ‖z‖ ^ b * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + 1 + (m : ℝ) / 2))
        ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + 1 + (m : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hzab (Real.rpow_nonneg hBpos.le _)
      _ = ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * s.re + 1)) / 2) := by
          rw [← Real.rpow_add hBpos]; congr 1; ring

private noncomputable def realVal (k : ℤ) (τ : ℝ) (s : ℂ) : ℂ :=
  (-Complex.I) ^ k * (Complex.Gammaℝ (2 * (s + (τ : ℂ) * Complex.I / 2))
      * Complex.Gammaℝ (2 * (s + (τ : ℂ) * Complex.I / 2) + 1))
    / (Complex.Gammaℝ (2 * (s + (τ : ℂ) * Complex.I / 2) + 1 + (k : ℂ))
      * Complex.Gammaℝ (2 * (s + (τ : ℂ) * Complex.I / 2) + 1 - (k : ℂ)))

private noncomputable def cxVal (ab : ℕ × ℕ × ℕ) (τ : ℝ) (s : ℂ) : ℂ :=
  if ab.1 = ab.2.1 then
    (Real.pi : ℂ) * ((ab.1).factorial : ℂ)
      * Complex.Gamma ((2 * s + 1 + ((ab.2.2 : ℕ) : ℂ) / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2) - 1 - (ab.1 : ℂ))
      / Complex.Gamma (2 * s + 1 + ((ab.2.2 : ℕ) : ℂ) / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2)
  else 0

private theorem good_realVal (k : ℤ) (τ : ℝ) : KIntP7.Good (realVal k τ) :=
  KIntP7.good_real_place k τ

private theorem good_cxVal (ab : ℕ × ℕ × ℕ) (habm : ab.1 + ab.2.1 ≤ ab.2.2) (τ : ℝ) : KIntP7.Good (cxVal ab τ) := by
  by_cases hab : ab.1 = ab.2.1
  · have h := KIntP7.good_complex_place ab.1 ab.2.2 (by omega) τ
    unfold cxVal
    simp only [if_pos hab]
    exact h
  · unfold cxVal
    simp only [if_neg hab]
    exact KIntP7.good_const 0

private theorem integral_Wr_eq (k : ℤ) (τ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, (((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2))
      = realVal k τ s := by
  have h := AutomorphicForm.LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal k
    (s + (τ : ℂ) * Complex.I / 2) (by simpa [Complex.div_ofNat_re] using hs)
  rw [show (s + (τ : ℂ) * Complex.I / 2 + 1 / 2 : ℂ) = s + 1 / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2 from by ring] at h
  exact h

private theorem integral_Wc_eq (ab : ℕ × ℕ × ℕ) (habm : ab.1 + ab.2.1 ≤ ab.2.2) (τ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    ∫ z : ℂ, z ^ ab.1 * (starRingEnd ℂ) z ^ ab.2.1
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + ((ab.2.2 : ℕ) : ℂ) / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2))
      = cxVal ab τ s := by
  have hm : ((ab.1 : ℝ) + ab.2.1) ≤ ab.2.2 := by exact_mod_cast habm
  have h := AutomorphicForm.LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg ab.1 ab.2.1
    (2 * s + 1 + ((ab.2.2 : ℕ) : ℂ) / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2)
    (by simp [Complex.div_ofNat_re]; linarith)
  rw [h]
  rfl

private noncomputable def archVal (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S) (j : Fin D.n)
    (s : ℂ) : ℂ :=
  (∏ i, realVal (D.kdat j i) (D.τr j i) s) * ∏ w, cxVal (D.abm j w) (D.τc j w) s

private theorem good_archVal (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S) (j : Fin D.n) :
    KIntP7.Good (archVal D j) :=
  KIntP7.good_mul
    (KIntP7.good_finset_prod Finset.univ (f := fun i s => realVal (D.kdat j i) (D.τr j i) s)
      fun _ _ => good_realVal _ _)
    (KIntP7.good_finset_prod Finset.univ (f := fun w s => cxVal (D.abm j w) (D.τc j w) s)
      fun w _ => good_cxVal _ (D.habm j w) _)

private theorem integrable_f (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S) (j : Fin D.n) (s : ℂ)
    (hs : 0 < s.re) :
    Integrable (fun p : mixedEmbedding.mixedSpace F => (∏ i, D.Wr j i s (p.1 i)) * ∏ w, D.Wc j w s (p.2 w)) := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  refine Integrable.mul_prod (f := fun x : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ i, D.Wr j i s (x i))
    (g := fun z : {w : InfinitePlace F // w.IsComplex} → ℂ => ∏ w, D.Wc j w s (z w)) ?_ ?_
  · rw [MeasureTheory.volume_pi]
    refine Integrable.fintype_prod (f := fun i x => D.Wr j i s x) fun i => ?_
    rw [show (D.Wr j i s) = _ from funext (D.hWr j i s)]
    exact integrable_Wr _ _ s hs
  · rw [MeasureTheory.volume_pi]
    refine Integrable.fintype_prod (f := fun w z => D.Wc j w s z) fun w => ?_
    rw [show (D.Wc j w s) = _ from funext (D.hWc j w s)]
    exact integrable_Wc _ _ _ (D.habm j w) _ s hs

private theorem integral_f_eq_archVal (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S) (j : Fin D.n)
    (s : ℂ) (hs : 0 < s.re) :
    ∫ p : mixedEmbedding.mixedSpace F, (∏ i, D.Wr j i s (p.1 i)) * ∏ w, D.Wc j w s (p.2 w) = archVal D j s := by
  rw [MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.integral_prod_mul (fun x : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ i, D.Wr j i s (x i))
      (fun z : {w : InfinitePlace F // w.IsComplex} → ℂ => ∏ w, D.Wc j w s (z w)),
    MeasureTheory.volume_pi, MeasureTheory.volume_pi,
    MeasureTheory.integral_fintype_prod_eq_prod (fun i x => D.Wr j i s x),
    MeasureTheory.integral_fintype_prod_eq_prod (fun w z => D.Wc j w s z)]
  unfold archVal
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp_rw [D.hWr j i s]
    exact integral_Wr_eq _ _ s hs
  · refine Finset.prod_congr rfl fun w _ => ?_
    simp_rw [D.hWc j w s]
    exact integral_Wc_eq _ (D.habm j w) _ s hs

private theorem integrable_tensor
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (νf : Measure (FiniteAdeleRing (𝓞 F) F)) [νf.IsAddHaarMeasure]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μv v).IsAddHaarMeasure]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S)
    (j : Fin D.n) (s : ℂ) (hs : 1 / 2 < s.re) :
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    Integrable (fun x : AdeleRing (𝓞 F) F =>
        (((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
          * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)))
      (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) := by
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hs0 : 0 < s.re := by linarith
  have hfin := (EisensteinGeneral.Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod F νf S μv
    (fun v => D.h j v s) (fun v hv y hy => h_eq_one D j v hv s y hy) (fun v => integrable_h μv hϖ D j v s hs0)
    (summable_h μv hϖ D j s hs)).1
  exact EisensteinGeneral.Glue.integrable_mul_of_integrable_of_integrable F
    (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) νf
    (fun p : mixedEmbedding.mixedSpace F => (∏ i, D.Wr j i s (p.1 i)) * ∏ w, D.Wc j w s (p.2 w))
    (fun x => ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x v)) (integrable_f D j s hs0) hfin

private theorem per_datum_identity
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
    (nψ : HeightOneSpectrum (𝓞 F) → ℤ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S) :
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∃ R : ℂ → ℂ, KIntP7.Good R ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
            * weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (Ψ s) g
          = (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
            * R s := by
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F

  letI mK : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F) := fun v => borel _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F) := fun v => ⟨rfl⟩
  set μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F) := fun v => Measure.addHaar with hμv
  haveI hμvH : ∀ v, (μv v).IsAddHaarMeasure := fun v => by rw [hμv]; infer_instance
  letI mf : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  set νf : Measure (FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hνf

  set cbox : ℂ := ((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F (NumberField.AdelicBox.adelicBox F)).toReal : ℂ)
    with hcbox
  set cF : ℂ := (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) with hcF
  set ca : ℂ := ((((distribHaarChar (AdeleRing (𝓞 F) F) D.a : ℝ≥0) : ℝ) : ℂ))⁻¹ with hca
  have hcbox0 : cbox ≠ 0 := by
    rw [hcbox]
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos F).ne'
      (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top F).ne).ne'
  refine ⟨fun s => ca * cbox * cF * ∑ j : Fin D.n, D.C j s * archVal D j s * ∏ v ∈ S, placeVal D μv j v s, ?_, ?_⟩
  ·
    exact KIntP7.good_mul (KIntP7.good_const _)
      (KIntP7.good_finset_sum Finset.univ
        (f := fun j s => D.C j s * archVal D j s * ∏ v ∈ S, placeVal D μv j v s)
        fun j _ => KIntP7.good_mul (KIntP7.good_mul (KIntP7.good_of_differentiable (D.hC j)) (good_archVal D j))
          (KIntP7.good_finset_prod S (f := fun v s => placeVal D μv j v s) fun v _ => good_placeVal D μv j v))
  · intro s hs
    have hs0 : 0 < s.re := by linarith

    set G : AdeleRing (𝓞 F) F → ℂ := fun x => ∑ j : Fin D.n, D.C j s *
        (((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
          * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)) with hG
    have hW : weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (Ψ s) g
        = ∫ y, G (D.a • (y + D.u)) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) := by
      unfold weylIntertwiningIntegral
      rw [show (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F from by
        rw [adelicWeyl, ← map_inv, gl2Weyl_inv]]
      congr 1
      funext y
      rw [D.hfac s y]
      simp only [hG]
      exact Finset.sum_congr rfl fun j _ => by ring

    have hcv : ∫ y, G (D.a • (y + D.u)) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)
        = ca * ∫ z, G z ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) := by
      have h4 := EisensteinGeneral.Piece.integral_smul_add_mul_addChar_neg_mul_eq F 1 G D.a D.u 0
      simp only [AddChar.one_apply, mul_one] at h4
      rw [hca]
      exact h4

    have hint : ∀ j : Fin D.n, Integrable (fun x : AdeleRing (𝓞 F) F =>
        (((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
          * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)))
        (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) :=
      fun j => integrable_tensor νf μv hϖ D j s hs
    have hsum : ∫ z, G z ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)
        = ∑ j : Fin D.n, D.C j s * ∫ x, (((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
          * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) := by
      simp only [hG]
      rw [integral_finsetSum _ (fun j _ => (hint j).const_mul (D.C j s))]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

    have hval : ∀ j : Fin D.n,
        (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
            * ∫ x, (((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
          * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)
          = cbox * cF * archVal D j s * (∏ v ∈ S, placeVal D μv j v s)
            * (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) := by
      intro j
      have h0 :=
        open AutomorphicForm.LocalIntertwining in
        integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
        F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) S μv
        (fun p : mixedEmbedding.mixedSpace F => (∏ i, D.Wr j i s (p.1 i)) * ∏ w, D.Wc j w s (p.2 w))
        (fun v => D.h j v s) ϖ (fun v _ => hϖ v) (fun v => NumberField.TateGlobal.localChar χ v)
        (fun v hv => D.hχS v hv) (fun v _ => (D.hχϖ v).le) s hs
      have hsplit : (fun x : AdeleRing (𝓞 F) F =>
          ((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
            * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
            * ((∏ v ∈ S, D.h j v s (x.2 v))
              * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                  ((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x.2 v.1)
          + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v.1)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x.2 v.1))))
            = fun x => (((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
          * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)) := by
        funext x
        rw [finprod_h_eq D j s x]
      rw [hsplit, integral_f_eq_archVal D j s hs0,
        Finset.prod_congr rfl (fun v hv => inv_vol_mul_integral_h_eq μv hϖ D j v hv s hs0)] at h0
      rw [← hcbox, ← hcF] at h0
      calc (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
              * ∫ x, (((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
          * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)
          = cbox * (cbox⁻¹ * (∫ x, (((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
          * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F))
              * (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))) := by
            rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hcbox0, one_mul, mul_comm]
        _ = cbox * (cF * archVal D j s * ((∏ v ∈ S, placeVal D μv j v s)
              * (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))))) := by rw [h0]
        _ = _ := by ring

    rw [hW, hcv, hsum]
    have step1 : (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
          * (ca * ∑ j : Fin D.n, D.C j s
            * ∫ x, (((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
          * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F))
        = ca * ∑ j : Fin D.n, D.C j s * ((∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
            * ∫ x, (((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
          * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have step2 : ca * ∑ j : Fin D.n, D.C j s * ((∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
            * ∫ x, (((∏ i, D.Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 i))
          * ∏ w, D.Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), D.h j v s (x.2 v)) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F))
        = ca * ∑ j : Fin D.n, D.C j s * (cbox * cF * archVal D j s * (∏ v ∈ S, placeVal D μv j v s)
            * (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))) := by
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hval j]
    have step3 : ca * ∑ j : Fin D.n, D.C j s * (cbox * cF * archVal D j s * (∏ v ∈ S, placeVal D μv j v s)
            * (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))))
        = (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
          * (ca * cbox * cF * ∑ j : Fin D.n, D.C j s * archVal D j s * ∏ v ∈ S, placeVal D μv j v s) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [step1, step2, step3]

end

end KIntC

open AutomorphicForm in

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (g : AdelicGL2 (𝓞 F) F),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F)))
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
      (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
      ∃ R : ℂ → ℂ, MeromorphicOn R Set.univ ∧ DifferentiableOn ℂ R {s : ℂ | 0 < s.re} ∧
        ∀ s : ℂ, 1 / 2 < s.re →
          (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
            * weylIntertwiningIntegral (𝓞 F) F
                (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (φ s) g
          = (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
            * R s := by
  intro α hα μ ν hμ hν φ hφ hφK hφf hφjc hφhol g

  letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F

  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ,
      ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
    have key : ∀ v : HeightOneSpectrum (𝓞 F),
        ∃ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
      intro v
      obtain ⟨r, hr⟩ := v.valuation_exists_uniformizer' F

      obtain ⟨x, hx⟩ : ∃ x : v.adicCompletion F, Valued.v x = WithZero.exp (-1 : ℤ) := by
        exact ⟨_, (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation v r).trans hr⟩
      have hne : x ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hx
        exact WithZero.exp_ne_zero hx.symm
      refine ⟨Units.mk0 x hne, ?_⟩
      exact hx
    choose ϖ hϖ using key
    exact ⟨ϖ, hϖ⟩

  have hzero : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, (∀ x, f x = 0) →
      weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) f g = 0 := by
    intro f hf
    simp only [weylIntertwiningIntegral, hf, MeasureTheory.integral_zero]
  have hgood0 : KIntP7.Good fun _ : ℂ => (0 : ℂ) := KIntP7.good_const 0
  by_cases hz : ∀ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), φ s x = 0
  · refine ⟨∅, ϖ, hϖ, fun _ => 0, hgood0.1, hgood0.2, ?_⟩
    intro s _
    rw [hzero (φ s) (hz s), mul_zero, mul_zero]
  · push Not at hz
    obtain ⟨s₀, g₀, hne⟩ := hz

    have hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ) :=
      NumberField.TateGlobal.continuous_ideleNorm F
    have hφ₀c : Continuous (φ s₀) :=
      hφjc.comp (continuous_const.prodMk continuous_id)
    obtain ⟨hμc, hνc⟩ :=
      EisensteinGeneral.Piece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero
        F α hα hαc μ ν s₀ (φ s₀) (hφ s₀) hφ₀c g₀ hne

    obtain ⟨n, c, ψ, hc, hψind, hψK, hψf, hψjc, hψhol, hψflat, hsum⟩ :=
      AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family
        F hα μ ν φ hφ hφK hφf hφjc hφhol

    have hψglob := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar F
    obtain ⟨ψv, nψ, θr, θc, hψv, hψv', hnψfin, hψfin, hθr, hθc, hψarch⟩ :=
      AutomorphicForm.exists_localComponents_of_isGlobalAddChar F _ hψglob

    have hdat : ∀ i : Fin n, (∃ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), ψ i s x ≠ 0) →
        ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S →
          Nonempty (EisensteinGeneral.Piece.FactorizationDatum F ψv nψ (μ * ν⁻¹) ϖ (ψ i) g S) := by
      intro i hi
      refine EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum F hα μ ν hμ hν hμc hνc _ hψglob
        ψv nψ hnψfin hψv hψv' hψfin θr hθr θc hθc ?_ (μ * ν⁻¹) rfl ϖ hϖ (ψ i) (hψind i) (hψK i) (hψf i) (hψjc i)
        (hψhol i) (hψflat i) hi g
      intro p
      classical
      rw [hψarch p, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype]

    classical
    have hdat' : ∀ i : Fin n, ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
        (∃ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), ψ i s x ≠ 0) → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S →
          Nonempty (EisensteinGeneral.Piece.FactorizationDatum F ψv nψ (μ * ν⁻¹) ϖ (ψ i) g S) := by
      intro i
      by_cases hi : ∃ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), ψ i s x ≠ 0
      · obtain ⟨S₀, h⟩ := hdat i hi
        exact ⟨S₀, fun _ => h⟩
      · exact ⟨∅, fun h => absurd h hi⟩
    choose S₀ hS₀ using hdat'
    let S : Finset (HeightOneSpectrum (𝓞 F)) := Finset.univ.biUnion S₀
    have hsub : ∀ i, S₀ i ⊆ S := fun i => Finset.subset_biUnion_of_mem S₀ (Finset.mem_univ i)
    have hψc : ∀ (i : Fin n) (s : ℂ), Continuous (ψ i s) := fun i s =>
      (hψjc i).comp (continuous_const.prodMk continuous_id)

    have hR : ∀ i : Fin n, ∃ Ri : ℂ → ℂ, KIntP7.Good Ri ∧
        ∀ s : ℂ, 1 / 2 < s.re →
          (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
            * weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (ψ i s) g
          = (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
            * Ri s := by
      intro i
      by_cases hi : ∃ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), ψ i s x ≠ 0
      · obtain ⟨D⟩ := hS₀ i hi S (hsub i)
        exact KIntC.per_datum_identity ψv nψ (μ * ν⁻¹) ϖ hϖ (ψ i) g S D
      · push Not at hi
        refine ⟨fun _ => 0, hgood0, ?_⟩
        intro s _
        rw [hzero (ψ i s) (hi s), mul_zero, mul_zero]
    choose Ri hRi using hR

    have hM : ∀ s : ℂ, 1 / 2 < s.re →
        weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (φ s) g
          = ∑ i : Fin n, c i s
              * weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (ψ i s) g := by
      intro s hs
      simp only [weylIntertwiningIntegral]
      have hpt : (fun x : AdeleRing (𝓞 F) F => φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g))
          = fun x => ∑ i : Fin n, c i s * ψ i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g) :=
        funext fun x => hsum s _
      rw [hpt, MeasureTheory.integral_finsetSum]
      · simp only [MeasureTheory.integral_const_mul]
      · intro i _
        exact (AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν hμ hν s hs (ψ i s)
          (hψind i s) (hψc i s) g).const_mul (c i s)

    have hgood : KIntP7.Good fun s => ∑ i : Fin n, c i s * Ri i s :=
      KIntP7.good_finset_sum Finset.univ fun i _ =>
        KIntP7.good_mul (KIntP7.good_of_differentiable (hc i)) (hRi i).1
    refine ⟨S, ϖ, hϖ, fun s => ∑ i : Fin n, c i s * Ri i s, hgood.1, hgood.2, ?_⟩
    intro s hs
    rw [hM s hs, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, (hRi i).2 s hs, mul_left_comm]

end S_AutomorphicForm_exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul (solution)
