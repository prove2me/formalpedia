-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_and_sub_eq_cross_sub_and_sub_eq_zero_two_pairs_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/12370c27-aae8-5e09-98a4-a23759fd7cc8

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
import Theorems.Thm_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
import Theorems.Thm_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm
import Theorems.Thm_AutomorphicForm_integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa
import Theorems.Thm_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable
import Theorems.Thm_AutomorphicForm_memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half
import Theorems.Thm_AutomorphicForm_continuous_pseudoEisenstein_of_isInducedSection_of_re_gt_half
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_and_sub_eq_cross_sub_and_sub_eq_zero_two_pairs_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal AutomorphicForm
open scoped NNReal ENNReal Topology ComplexConjugate

noncomputable section

namespace R4TwoPairInc

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

theorem secondCountableTopology_units {M : Type*} [TopologicalSpace M] [Monoid M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountableTopology_ideles : SecondCountableTopology (𝔸)ˣ := by
  haveI : SecondCountableTopology 𝔸 := NumberField.AdeleRing.secondCountableTopology F
  exact secondCountableTopology_units

theorem measurable_ideleNorm' : Measurable (ideleNorm F) :=
  (NumberField.TateGlobal.continuous_ideleNorm F).measurable

variable {F}

theorem conj_unitary {χ : (𝔸)ˣ →* ℂˣ} (hχ : IsUnitaryChar (𝓞 F) F χ) (x : (𝔸)ˣ) :
    conj ((χ x : ℂˣ) : ℂ) = ((χ x : ℂˣ) : ℂ)⁻¹ :=
  (Complex.inv_eq_conj (hχ x)).symm

theorem conj_ofReal_cpow {r : ℝ} (hr : 0 ≤ r) (w : ℂ) :
    conj (((r : ℝ) : ℂ) ^ w) = ((r : ℝ) : ℂ) ^ (conj w) := by
  have harg : ((r : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr]; exact Real.pi_pos.ne
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

theorem conj_half : conj ((1 / 2 : ℂ)) = 1 / 2 := by
  rw [map_div₀, map_one, map_ofNat]

theorem conj_etaFst_val {μ : (𝔸)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ)
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (𝔸)ˣ) :
    conj ((etaFst μ α hα s x : ℂˣ) : ℂ)
      = ((μ x : ℂˣ) : ℂ)⁻¹ * (((α x : ℝˣ) : ℝ) : ℂ) ^ (conj s + 1 / 2) := by
  rw [etaFst_apply, Units.val_mul, map_mul, conj_unitary hμ, cpowChar_apply_val,
    conj_ofReal_cpow (hα x).le, map_add, conj_half]

theorem conj_etaSnd_val {ν : (𝔸)ˣ →* ℂˣ} (hν : IsUnitaryChar (𝓞 F) F ν)
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (𝔸)ˣ) :
    conj ((etaSnd ν α hα s x : ℂˣ) : ℂ)
      = ((ν x : ℂˣ) : ℂ)⁻¹ * (((α x : ℝˣ) : ℝ) : ℂ) ^ (-(conj s + 1 / 2)) := by
  rw [etaSnd_apply, Units.val_mul, map_mul, conj_unitary hν, cpowChar_apply_val,
    conj_ofReal_cpow (hα x).le, map_neg, map_add, conj_half]

theorem integrand_eq {μ ν μ' ν' : (𝔸)ˣ →* ℂˣ}
    (hμ' : IsUnitaryChar (𝓞 F) F μ') (hν' : IsUnitaryChar (𝓞 F) F ν')
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s s' : ℂ) (z t : (𝔸)ˣ) (A B : ℂ) :
    ((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ)
        * conj (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ))
        * A * B * ((((α t : ℝˣ) : ℝ)⁻¹ : ℝ) : ℂ)
      = (((μ t : ℂˣ) : ℂ) * ((μ' t : ℂˣ) : ℂ)⁻¹)
        * ((((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * ((μ' z : ℂˣ) : ℂ)⁻¹ * ((ν' z : ℂˣ) : ℂ)⁻¹)
          * (((α t : ℝˣ) : ℝ) : ℂ) ^ (s + conj s') * A * B) := by
  have hz : (((α z : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα z).ne'
  have ht : (((α t : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα t).ne'
  rw [map_mul (starRingEnd ℂ), conj_etaFst_val hμ', conj_etaSnd_val hν', etaFst_apply, etaSnd_apply]
  simp only [Units.val_mul, cpowChar_apply_val, map_mul, Complex.ofReal_mul, Complex.ofReal_inv, mul_inv,
    Complex.mul_cpow_ofReal_nonneg (hα z).le (hα t).le]

  have hzpow : (((α z : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) * (((α z : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2))
      * ((((α z : ℝˣ) : ℝ) : ℂ) ^ (conj s' + 1 / 2) * (((α z : ℝˣ) : ℝ) : ℂ) ^ (-(conj s' + 1 / 2))) = 1 := by
    rw [← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz, add_neg_cancel, add_neg_cancel,
      Complex.cpow_zero, mul_one]
  have htpow : (((α t : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) * (((α t : ℝˣ) : ℝ) : ℂ) ^ (conj s' + 1 / 2)
      * ((((α t : ℝˣ) : ℝ) : ℂ))⁻¹ = (((α t : ℝˣ) : ℝ) : ℂ) ^ (s + conj s') := by
    rw [← Complex.cpow_add _ _ ht, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ ht]
    congr 1; ring
  rw [← htpow]
  linear_combination
    (((μ z : ℂˣ) : ℂ) * ((μ t : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * ((μ' z : ℂˣ) : ℂ)⁻¹ * ((μ' t : ℂˣ) : ℂ)⁻¹
      * ((ν' z : ℂˣ) : ℂ)⁻¹ * A * B
      * ((((α t : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) * (((α t : ℝˣ) : ℝ) : ℂ) ^ (conj s' + 1 / 2)
        * ((((α t : ℝˣ) : ℝ) : ℂ))⁻¹)) * hzpow

variable (F)

def radial (R R' : ℝ) (W : ℂ) : ℝ → ℂ := fun r =>
  (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) r * ((r : ℝ) : ℂ) ^ W

theorem measurable_radial (R R' : ℝ) (W : ℂ) : Measurable (radial R R' W) := by
  unfold radial
  refine Measurable.mul (measurable_const.indicator measurableSet_Ioc) ?_
  exact (Complex.measurable_ofReal).pow_const W

theorem norm_radial_le (R R' : ℝ) (W : ℂ) (r : ℝ) :
    ‖radial R R' W r‖ ≤ (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℝ)) r
      * max (Real.exp R ^ W.re) (Real.exp R' ^ W.re) := by
  unfold radial
  by_cases hr : r ∈ Set.Ioc (Real.exp R) (Real.exp R')
  · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, one_mul, one_mul]
    have hr0 : 0 < r := (Real.exp_pos R).trans hr.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr0]
    rcases le_total 0 W.re with hW | hW
    · exact le_max_of_le_right (Real.rpow_le_rpow hr0.le hr.2 hW)
    · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos (Real.exp_pos R) hr.1.le hW)
  · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, zero_mul, zero_mul, norm_zero]

theorem integral_radial (R R' : ℝ) (hRR' : R ≤ R') (W : ℂ) (hW : W ≠ 0) :
    ∫ r in Set.Ioi (0 : ℝ), ((r : ℝ) : ℂ)⁻¹ * radial R R' W r
      = (Complex.exp ((R' : ℂ) * W) - Complex.exp ((R : ℂ) * W)) / W := by
  have hexp : Real.exp R ≤ Real.exp R' := Real.exp_le_exp.2 hRR'
  have hsub : Set.Ioc (Real.exp R) (Real.exp R') ⊆ Set.Ioi 0 := fun r hr => (Real.exp_pos R).trans hr.1
  have hind : (fun r : ℝ => ((r : ℝ) : ℂ)⁻¹ * radial R R' W r)
      = (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun r => ((r : ℝ) : ℂ) ^ (W - 1)) := by
    funext r
    unfold radial
    by_cases hr : r ∈ Set.Ioc (Real.exp R) (Real.exp R')
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, one_mul]
      have hr0 : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ((Real.exp_pos R).trans hr.1).ne'
      rw [Complex.cpow_sub _ _ hr0, Complex.cpow_one, div_eq_mul_inv, mul_comm]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]; simp
  rw [hind, setIntegral_indicator measurableSet_Ioc, Set.inter_eq_self_of_subset_right hsub,
    ← intervalIntegral.integral_of_le hexp, integral_cpow]
  · rw [sub_add_cancel]
    have h1 : ((Real.exp R' : ℝ) : ℂ) ^ W = Complex.exp ((R' : ℂ) * W) := by
      rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
        Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_pos.le)]
    have h2 : ((Real.exp R : ℝ) : ℂ) ^ W = Complex.exp ((R : ℂ) * W) := by
      rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
        Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_pos.le)]
    rw [h1, h2]
  · right
    refine ⟨by simpa using hW, ?_⟩
    rw [Set.uIcc_of_le hexp]
    exact fun h => (lt_irrefl (0 : ℝ)) ((Real.exp_pos R).trans_le h.1)

theorem integrableOn_radial (R R' : ℝ) (W : ℂ) :
    IntegrableOn (fun r : ℝ => ((r : ℝ) : ℂ)⁻¹ * radial R R' W r) (Set.Ioi 0) := by
  have hind : (fun r : ℝ => ((r : ℝ) : ℂ)⁻¹ * radial R R' W r)
      = (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun r => ((r : ℝ) : ℂ)⁻¹ * ((r : ℝ) : ℂ) ^ W) := by
    funext r
    unfold radial
    by_cases hr : r ∈ Set.Ioc (Real.exp R) (Real.exp R')
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, one_mul]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, zero_mul, mul_zero]
  rw [hind]
  refine Integrable.integrableOn ((integrable_indicator_iff measurableSet_Ioc).2 ?_)
  have hcont : ContinuousOn (fun r : ℝ => ((r : ℝ) : ℂ)⁻¹ * ((r : ℝ) : ℂ) ^ W)
      (Set.Icc (Real.exp R) (Real.exp R')) := by
    intro r hr
    have hr0 : 0 < r := (Real.exp_pos R).trans_le hr.1
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul ?_ ?_
    · exact (Complex.continuous_ofReal.continuousAt).inv₀ (Complex.ofReal_ne_zero.mpr hr0.ne')
    · exact (Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
        (Or.inl (by simpa using hr0))
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

theorem band_integral
    (D D' : Set (𝔸)ˣ) (a b : ℝ)
    (Cs : ℝ≥0∞) (hCs_top : Cs ≠ ∞)
    (hCs : ∀ r : ℝ, 0 < r →
      (NumberField.Idele.idelicHaar F) (D ∩ {z | ideleNorm F z ^ 2 * r ∈ Set.Icc a b}) = Cs)
    (Cn : ℝ)
    (hCn : ∀ g : ℝ → ℂ, Measurable g →
      (IntegrableOn (fun x => g (ideleNorm F x)) D' (NumberField.Idele.idelicHaar F) ↔
          IntegrableOn (fun r : ℝ => (r : ℂ)⁻¹ * g r) (Set.Ioi (0 : ℝ))) ∧
        ∫ x in D', g (ideleNorm F x) ∂(NumberField.Idele.idelicHaar F) =
          Cn * ∫ r in Set.Ioi (0 : ℝ), (r : ℂ)⁻¹ * g r)
    (W : ℂ) (hW : W ≠ 0) (R R' : ℝ) (hRR' : R ≤ R') :
    ∫ z in D, ∫ t in D',
        (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t)
          * ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t)
            * ((ideleNorm F t : ℝ) : ℂ) ^ W)
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
      = (Cs.toReal : ℂ) * Cn * ((Complex.exp ((R' : ℂ) * W) - Complex.exp ((R : ℂ) * W)) / W) := by
  set ν := NumberField.Idele.idelicHaar F with hν
  set G : (𝔸)ˣ → ℂ := fun t => radial R R' W (ideleNorm F t) with hG
  set S : (𝔸)ˣ → Set (𝔸)ˣ := fun t => {z | ideleNorm F z ^ 2 * ideleNorm F t ∈ Set.Icc a b} with hS
  have hSm : ∀ t, MeasurableSet (S t) := fun t =>
    (((measurable_ideleNorm' F).pow_const 2).mul_const _) measurableSet_Icc
  have hind : ∀ z t, (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t)
      = (S t).indicator (fun _ => (1 : ℂ)) z := by
    intro z t
    by_cases h : ideleNorm F z ^ 2 * ideleNorm F t ∈ Set.Icc a b
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show z ∈ S t from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show z ∉ S t from h)]
  have hGm : Measurable G := (measurable_radial R R' W).comp (measurable_ideleNorm' F)

  set Φ : (𝔸)ˣ → (𝔸)ˣ → ℂ := fun z t => (S t).indicator (fun _ => (1 : ℂ)) z * G t with hΦ
  have hΦeq : ∀ z t, (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t)
      * ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t)
        * ((ideleNorm F t : ℝ) : ℂ) ^ W) = Φ z t := by
    intro z t; simp only [hΦ, hG, radial, hind]
  simp_rw [hΦeq]

  have hGint : IntegrableOn G D' ν := by
    have := (hCn (radial R R' W) (measurable_radial R R' W)).1
    exact this.2 (integrableOn_radial R R' W)

  have hνS : ∀ t, ν (D ∩ S t) = Cs := fun t => hCs (ideleNorm F t) (ideleNorm_pos t)
  have hνS' : ∀ t, (ν.restrict D) (S t) = Cs := fun t => by
    rw [Measure.restrict_apply (hSm t), Set.inter_comm, hνS]

  have hinner : ∀ t, ∫ z in D, Φ z t ∂ν = (Cs.toReal : ℂ) * G t := by
    intro t
    simp only [hΦ]
    rw [integral_mul_const, integral_indicator_const _ (hSm t), measureReal_def, hνS',
      Complex.real_smul, mul_one]
  have hinner_norm : ∀ t, ∫ z in D, ‖Φ z t‖ ∂ν = Cs.toReal * ‖G t‖ := by
    intro t
    have : (fun z => ‖Φ z t‖) = fun z => (S t).indicator (fun _ => ‖G t‖) z := by
      funext z
      simp only [hΦ]
      by_cases hz : z ∈ S t
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul, norm_zero]
    rw [this, integral_indicator_const _ (hSm t), measureReal_def, hνS', smul_eq_mul]

  haveI : SecondCountableTopology (𝔸)ˣ := secondCountableTopology_ideles F
  haveI : SigmaFinite ν := by rw [hν]; infer_instance
  have hmeasΦ : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable fun p : (𝔸)ˣ × (𝔸)ˣ => ideleNorm F p.1 ^ 2 * ideleNorm F p.2 :=
      (((measurable_ideleNorm' F).comp measurable_fst).pow_const 2).mul
        ((measurable_ideleNorm' F).comp measurable_snd)
    have h2 : Measurable fun p : (𝔸)ˣ × (𝔸)ˣ =>
        (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F p.1 ^ 2 * ideleNorm F p.2) :=
      (measurable_const.indicator measurableSet_Icc).comp h1
    have h3 : Measurable fun p : (𝔸)ˣ × (𝔸)ˣ => G p.2 := hGm.comp measurable_snd
    have : Function.uncurry Φ = fun p : (𝔸)ˣ × (𝔸)ˣ =>
        (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F p.1 ^ 2 * ideleNorm F p.2) * G p.2 := by
      funext p; simp only [Function.uncurry, hΦ, hind]
    rw [this]
    exact h2.mul h3
  have hint : Integrable (Function.uncurry Φ) ((ν.restrict D).prod (ν.restrict D')) := by
    refine (integrable_prod_iff' hmeasΦ.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall fun t => ?_
      show Integrable (fun z => (S t).indicator (fun _ => (1 : ℂ)) z * G t) (ν.restrict D)
      have : (fun z => (S t).indicator (fun _ => (1 : ℂ)) z * G t)
          = (S t).indicator (fun _ => G t) := by
        funext z
        by_cases hz : z ∈ S t
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
      rw [this, integrable_indicator_iff (hSm t)]
      refine integrableOn_const ?_
      rw [hνS']; exact hCs_top
    · have : (fun t => ∫ z, ‖Function.uncurry Φ (z, t)‖ ∂(ν.restrict D)) = fun t => Cs.toReal * ‖G t‖ := by
        funext t; exact hinner_norm t
      rw [this]
      exact (hGint.norm.const_mul _)

  have hswap : ∫ z in D, ∫ t in D', Φ z t ∂ν ∂ν = ∫ t in D', ∫ z in D, Φ z t ∂ν ∂ν :=
    integral_integral_swap hint
  rw [hswap]
  simp_rw [hinner]
  rw [integral_const_mul]

  have ht : ∫ t in D', G t ∂ν = Cn * ∫ r in Set.Ioi (0 : ℝ), ((r : ℝ) : ℂ)⁻¹ * radial R R' W r :=
    (hCn (radial R R' W) (measurable_radial R R' W)).2
  rw [ht, integral_radial R R' hRR' W hW]
  ring

theorem twisted_band_integral_eq_zero
    (D D' : Set (𝔸)ˣ)
    (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
    (χ : (𝔸)ˣ →* ℂˣ) (hχF : IsIdeleClassChar (𝓞 F) F χ)
    (hχ : ∃ z : (𝔸)ˣ, ideleNorm F z = 1 ∧ χ z ≠ 1)
    (h : (𝔸)ˣ → ℝ → ℂ) :
    ∫ z in D, ∫ t in D', ((χ t : ℂˣ) : ℂ) * h z (ideleNorm F t)
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) = 0 := by
  have hz : ∀ z, ∫ t in D', ((χ t : ℂˣ) : ℂ) * h z (ideleNorm F t) ∂(NumberField.Idele.idelicHaar F) = 0 :=
    fun z =>
      NumberField.TateGlobal.setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
        F (NumberField.Idele.idelicHaar F) D' hD'F χ hχF hχ (h z)
  simp_rw [hz]
  exact integral_zero _ _

theorem ztwisted_band_integral_eq_zero
    (D D' : Set (𝔸)ˣ)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (ω : (𝔸)ˣ →* ℂˣ) (hωF : IsIdeleClassChar (𝓞 F) F ω)
    (hω : ∃ z : (𝔸)ˣ, ideleNorm F z = 1 ∧ ω z ≠ 1)
    (h : ℝ → (𝔸)ˣ → ℂ) :
    ∫ z in D, ∫ t in D', ((ω z : ℂˣ) : ℂ) * h (ideleNorm F z) t
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) = 0 := by
  have hz : ∀ z, ∫ t in D', ((ω z : ℂˣ) : ℂ) * h (ideleNorm F z) t ∂(NumberField.Idele.idelicHaar F)
      = ((ω z : ℂˣ) : ℂ) * ∫ t in D', h (ideleNorm F z) t ∂(NumberField.Idele.idelicHaar F) :=
    fun z => integral_const_mul _ _
  simp_rw [hz]
  exact NumberField.TateGlobal.setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
    F (NumberField.Idele.idelicHaar F) D hDF ω hωF hω
    (fun r => ∫ t in D', h r t ∂(NumberField.Idele.idelicHaar F))

theorem omega_ne_one {G : Type*} [CommGroup G] {a b a' b' : G} (h1 : a * a'⁻¹ = 1) (h2 : b ≠ b') :
    a * b * a'⁻¹ * b'⁻¹ ≠ 1 := by
  rw [mul_right_comm a b a'⁻¹, h1, one_mul]
  exact fun h => h2 (mul_inv_eq_one.1 h)

theorem like_band
    (αm : (𝔸)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)) (hαI : ∀ t : (𝔸)ˣ, ((αm t : ℝˣ) : ℝ) = ideleNorm F t)
    (D : Set (𝔸)ˣ) (hDm : MeasurableSet D) (aa bb : ℝ)
    (Cs : ℝ≥0∞) (hCs_top : Cs ≠ ∞)
    (hCs : ∀ r : ℝ, 0 < r →
      (NumberField.Idele.idelicHaar F) (D ∩ {z | ideleNorm F z ^ 2 * r ∈ Set.Icc aa bb}) = Cs)
    (Cn : ℝ)
    (hCn : ∀ g : ℝ → ℂ, Measurable g →
      (IntegrableOn (fun x => g (ideleNorm F x)) D (NumberField.Idele.idelicHaar F) ↔
          IntegrableOn (fun r : ℝ => (r : ℂ)⁻¹ * g r) (Set.Ioi (0 : ℝ))) ∧
        ∫ x in D, g (ideleNorm F x) ∂(NumberField.Idele.idelicHaar F) =
          Cn * ∫ r in Set.Ioi (0 : ℝ), (r : ℂ)⁻¹ * g r)
    {κ₁ κ₂ : (𝔸)ˣ →* ℂˣ} (hκ₁ : IsUnitaryChar (𝓞 F) F κ₁) (hκ₂ : IsUnitaryChar (𝓞 F) F κ₂)
    (a b : ℂ) (hW : a + conj b ≠ 0) (R R' : ℝ) (hRR' : R ≤ R') :
    (∫ z in D, ∫ t in D,
        ((etaFst κ₁ αm hαm a (z * t) : ℂˣ) : ℂ) * ((etaSnd κ₂ αm hαm a z : ℂˣ) : ℂ) *
              conj (((etaFst κ₁ αm hαm b (z * t) : ℂˣ) : ℂ) * ((etaSnd κ₂ αm hαm b z : ℂˣ) : ℂ)) *
            (Set.Icc aa bb).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
            (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
            (((ideleNorm F t)⁻¹ : ℝ) : ℂ) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
      = (Cs.toReal : ℂ) * Cn *
        ((Complex.exp ((R' : ℂ) * (a + conj b)) - Complex.exp ((R : ℂ) * (a + conj b))) / (a + conj b)) := by
  rw [← band_integral F D D aa bb Cs hCs_top hCs Cn hCn (a + conj b) hW R R' hRR']
  refine setIntegral_congr_fun hDm fun z _ => setIntegral_congr_fun hDm fun t _ => ?_
  rw [← hαI t]
  refine (integrand_eq (μ := κ₁) (ν := κ₂) (μ' := κ₁) (ν' := κ₂) hκ₁ hκ₂ αm hαm a b z t
    ((Set.Icc aa bb).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ((αm t : ℝˣ) : ℝ)))
    ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) ((αm t : ℝˣ) : ℝ))).trans ?_
  have h1 : ((κ₁ t : ℂˣ) : ℂ) * ((κ₁ t : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
  have h2 : ((κ₁ z : ℂˣ) : ℂ) * ((κ₂ z : ℂˣ) : ℂ) * ((κ₁ z : ℂˣ) : ℂ)⁻¹ * ((κ₂ z : ℂˣ) : ℂ)⁻¹ = 1 := by
    field_simp
  rw [h1, h2, one_mul, one_mul]
  ring

theorem dead_band
    (αm : (𝔸)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)) (hαI : ∀ t : (𝔸)ˣ, ((αm t : ℝˣ) : ℝ) = ideleNorm F t)
    (D : Set (𝔸)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (aa bb : ℝ)
    {κ₁ κ₂ κ₁' κ₂' : (𝔸)ˣ →* ℂˣ}
    (hκ₁' : IsUnitaryChar (𝓞 F) F κ₁') (hκ₂' : IsUnitaryChar (𝓞 F) F κ₂')
    (hκ₁F : IsIdeleClassChar (𝓞 F) F κ₁) (hκ₂F : IsIdeleClassChar (𝓞 F) F κ₂)
    (hκ₁'F : IsIdeleClassChar (𝓞 F) F κ₁') (hκ₂'F : IsIdeleClassChar (𝓞 F) F κ₂')
    (hex : ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, κ₁' z ≠ κ₁ z ∨ κ₂' z ≠ κ₂ z)
    (a b : ℂ) (R R' : ℝ) :
    (∫ z in D, ∫ t in D,
        ((etaFst κ₁ αm hαm a (z * t) : ℂˣ) : ℂ) * ((etaSnd κ₂ αm hαm a z : ℂˣ) : ℂ) *
              conj (((etaFst κ₁' αm hαm b (z * t) : ℂˣ) : ℂ) * ((etaSnd κ₂' αm hαm b z : ℂˣ) : ℂ)) *
            (Set.Icc aa bb).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
            (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
            (((ideleNorm F t)⁻¹ : ℝ) : ℂ) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)) = 0 := by
  have hcls : ∀ {χ₁ χ₂ : (𝔸)ˣ →* ℂˣ}, IsIdeleClassChar (𝓞 F) F χ₁ → IsIdeleClassChar (𝓞 F) F χ₂ →
      IsIdeleClassChar (𝓞 F) F (χ₁ * χ₂⁻¹) := fun h₁ h₂ u => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h₁ u, h₂ u, inv_one, mul_one]

  set χ : (𝔸)ˣ →* ℂˣ := κ₁ * κ₁'⁻¹ with hχdef
  set ω : (𝔸)ˣ →* ℂˣ := κ₁ * κ₂ * κ₁'⁻¹ * κ₂'⁻¹ with hωdef
  have hχF : IsIdeleClassChar (𝓞 F) F χ := hcls hκ₁F hκ₁'F
  have hωF : IsIdeleClassChar (𝓞 F) F ω := fun u => by
    simp only [hωdef, MonoidHom.mul_apply, MonoidHom.inv_apply, hκ₁F u, hκ₂F u, hκ₁'F u, hκ₂'F u, inv_one, mul_one]
  set rest : ℝ → (𝔸)ˣ → ℂ := fun r t =>
    (((αm t : ℝˣ) : ℝ) : ℂ) ^ (a + conj b) * (Set.Icc aa bb).indicator (fun _ => (1 : ℂ)) (r ^ 2 * ideleNorm F t) *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) with hrest
  have hpt : ∀ z t : (𝔸)ˣ,
      ((etaFst κ₁ αm hαm a (z * t) : ℂˣ) : ℂ) * ((etaSnd κ₂ αm hαm a z : ℂˣ) : ℂ) *
              conj (((etaFst κ₁' αm hαm b (z * t) : ℂˣ) : ℂ) * ((etaSnd κ₂' αm hαm b z : ℂˣ) : ℂ)) *
            (Set.Icc aa bb).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
            (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
            (((ideleNorm F t)⁻¹ : ℝ) : ℂ)
        = ((χ t : ℂˣ) : ℂ) * (((ω z : ℂˣ) : ℂ) * rest (ideleNorm F z) t) := by
    intro z t
    rw [← hαI t]
    refine (integrand_eq (μ := κ₁) (ν := κ₂) (μ' := κ₁') (ν' := κ₂') hκ₁' hκ₂' αm hαm a b z t
      ((Set.Icc aa bb).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ((αm t : ℝˣ) : ℝ)))
      ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) ((αm t : ℝˣ) : ℝ))).trans ?_
    simp only [hχdef, hωdef, hrest, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
      Units.val_inv_eq_inv_val, hαI]
    ring
  by_cases hχ : ∃ z : (𝔸)ˣ, ideleNorm F z = 1 ∧ χ z ≠ 1
  ·
    rw [← twisted_band_integral_eq_zero F D D hDF χ hχF hχ
      (fun z r => ((ω z : ℂˣ) : ℂ) * ((((r : ℝ) : ℂ) ^ (a + conj b)) *
        (Set.Icc aa bb).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * r) *
        (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) r))]
    refine setIntegral_congr_fun hDm fun z _ => setIntegral_congr_fun hDm fun t _ => ?_
    rw [hpt z t]
    simp only [hrest, hαI]
  ·
    push Not at hχ
    obtain ⟨z₀, hz₀m, hor⟩ := hex
    have hz₀ : ideleNorm F z₀ = 1 := (NumberField.TateGlobal.mem_normOneIdeles_iff z₀).mp hz₀m
    have h1 : κ₁ z₀ * (κ₁' z₀)⁻¹ = 1 := by
      have := hχ z₀ hz₀
      simpa [hχdef] using this
    have h1' : κ₁' z₀ = κ₁ z₀ := (mul_inv_eq_one.1 h1).symm
    have h2 : κ₂ z₀ ≠ κ₂' z₀ := by
      rcases hor with h | h
      · exact absurd h1' h
      · exact fun e => h e.symm
    have hω : ∃ z : (𝔸)ˣ, ideleNorm F z = 1 ∧ ω z ≠ 1 := by
      refine ⟨z₀, hz₀, ?_⟩
      have := omega_ne_one (a := κ₁ z₀) (b := κ₂ z₀) (a' := κ₁' z₀) (b' := κ₂' z₀) h1 h2
      simpa [hωdef] using this
    rw [← ztwisted_band_integral_eq_zero F D D hDF ω hωF hω
      (fun r t => ((χ t : ℂˣ) : ℂ) * rest r t)]
    refine setIntegral_congr_fun hDm fun z _ => setIntegral_congr_fun hDm fun t _ => ?_
    rw [hpt z t]
    ring

end R4TwoPairInc

end

noncomputable section

namespace R4TwoPairInc

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

open NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

theorem peterssonIntegral_zero (S : Set (AdelicGL2 (𝓞 F) F)) (x y : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F 0 S x y = ∫ g in S, x g * conj (y g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  unfold peterssonIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]

variable {F}

theorem memLp_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} {p : ℝ≥0∞}
    (hf : MemLp f p μ) : MemLp (fun x => conj (f x)) p μ := by
  refine hf.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hf.1) ?_
  exact Filter.Eventually.of_forall fun x => by simp

theorem isPrincipalTrivial_alpha :
    IsPrincipalTrivial (R := 𝓞 F) (K := F)
      (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits) := by
  intro u
  apply Units.ext
  show ((distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (algebraMap F 𝔸 : F →* 𝔸) u) : ℝ≥0) : ℝ) = 1
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
  have : Units.map (algebraMap F 𝔸).toMonoidHom u = Units.map (algebraMap F 𝔸 : F →* 𝔸) u := rfl
  rw [this] at h
  rw [h]; rfl

theorem section_borel_invariant
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α)
    {μ ν : (𝔸)ˣ →* ℂˣ} (hμF : IsIdeleClassChar (𝓞 F) F μ) (hνF : IsIdeleClassChar (𝓞 F) F ν)
    (s : ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) :
    ∀ b ∈ borelSubgroup F, ∀ y : AdelicGL2 (𝓞 F) F, φ (globalPoints (𝓞 F) F b * y) = φ y := by
  intro b hb y
  have hmem := globalPoints_mem_adelicBorel (𝓞 F) F hb
  rw [hφ (globalPoints (𝓞 F) F b) hmem y, borelDiagFst_globalPoints (𝓞 F) F hb hmem,
    borelDiagSnd_globalPoints (𝓞 F) F hb hmem, etaFst_isIdeleClassChar hμF hprin s,
    etaSnd_isIdeleClassChar hνF hprin s]
  simp

end R4TwoPairInc

end

open MeasureTheory NumberField NumberField.TateGlobal AutomorphicForm
open NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain
open scoped NNReal ENNReal Topology ComplexConjugate
open R4TwoPairInc

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

set_option maxHeartbeats 6400000 in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
    ∀ (μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμ' : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ') (_hν' : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν')
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμ'F : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ') (_hν'F : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν')
      (s s' : ℂ) (_hs : 1 / 2 < s.re) (_hs' : 1 / 2 < s'.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ' αm hαm s') (AutomorphicForm.etaSnd ν' αm hαm s') ψ)
      (_hψc : Continuous ψ) (_hψK : AutomorphicForm.IsArchKFinite F ψ) (_hψf : AutomorphicForm.IsKfSmooth F ψ),
    ∀ R R' : ℝ, R₀ ≤ R → R ≤ R' →
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F ψ) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      (μ' = μ → ν' = ν → μ = ν → s ≠ conj s' →
      ((∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) -
       (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F))) =
      (c : ℂ) *
        (( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s + conj s'))) / (s + conj s')
          + (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s - conj s'))) / (s - conj s') ) -
         ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s + conj s'))) / (s + conj s')
          + (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s - conj s'))) / (s - conj s') ))) ∧
      (μ' = μ → ν' = ν → (∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) →
      ((∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) -
       (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F))) =
      (c : ℂ) *
        (( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s + conj s'))) / (s + conj s') ) -
         ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s + conj s'))) / (s + conj s') ))) ∧
      (μ' = ν → ν' = μ → (∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) → s ≠ conj s' →
      ((∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) -
       (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F))) =
      (c : ℂ) *
        (( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s - conj s'))) / (s - conj s') ) -
         ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s - conj s'))) / (s - conj s') ))) ∧
      ((∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ' z ≠ μ z ∨ ν' z ≠ ν z) →
        (∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ' z ≠ ν z ∨ ν' z ≠ μ z) →
      ((∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) -
       (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F))) = 0) := by
  intro αm hαm

  dsimp only [productionPinsOf]

  set Haar : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hHaar
  set νb : Measure (AdeleRing (𝓞 F) F) := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F) with hνb
  set H : AdelicGL2 (𝓞 F) F → ℝ := adelicHeight F with hH
  set Φ₀ : Set (AdelicGL2 (𝓞 F) F) := canonicalTruncationDomain F α β with hΦ₀
  set Λ : ℝ → (AdelicGL2 (𝓞 F) F → ℂ) → AdelicGL2 (𝓞 F) F → ℂ := fun R f =>
    AutomorphicForm.lambdaT νb (fun t => AutomorphicForm.unipotentGL2 t) H (Real.exp R) f with hΛ
  set vC : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)) with hvC
  set νI : Measure (AdeleRing (𝓞 F) F)ˣ := NumberField.Idele.idelicHaar F with hνI
  set X0 : Set (AdelicGL2 (𝓞 F) F) :=
    {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hX0
  have hαI : ∀ t : (AdeleRing (𝓞 F) F)ˣ, ((αm t : ℝˣ) : ℝ) = ideleNorm F t := fun t => rfl
  have hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) αm := isPrincipalTrivial_alpha

  obtain ⟨hc0, hTc, hΦS, hΦslab, hΦfd⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum F α β hα hαβ
  obtain ⟨R₁, hR₁⟩ :=
    AutomorphicForm.peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm F α β hα
      (canonicalTruncationFloor F α β) (canonicalTruncationWindow F α β) (canonicalTruncationLowerCut F α β)
      (canonicalTruncationUpperCut F α β) hc0 (canonicalTruncationTranslates F α β) hTc Φ₀ hΦS hΦslab hΦfd

  obtain ⟨cT, hcT0, hcTtop, hcT⟩ :=
    AutomorphicForm.exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa F
  obtain ⟨D, hDm, hDF, -⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow F νI
  have hDF' : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range D νI := hDF
  obtain ⟨Cs, hCs0, hCstop, hCs⟩ :=
    NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const F D hDm hDF α β hα hαβ
  obtain ⟨Cn, hCn0, hCn⟩ :=
    NumberField.TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
      F νI
  have hCnD := (hCn D hDF').1
  have hcTpos : 0 < cT.toReal := ENNReal.toReal_pos hcT0 hcTtop
  have hCspos : 0 < Cs.toReal := ENNReal.toReal_pos hCs0 hCstop
  refine ⟨cT.toReal * Cs.toReal * Cn, by positivity, R₁, ?_⟩
  intro μ ν μ' ν' hμ hν hμ' hν' hμF hνF hμ'F hν'F s s' hs hs' φ hφ hφc hφK hφf ψ hψ hψc hψK hψf R R' hR hRR'

  set E : AdelicGL2 (𝓞 F) F → ℂ := pseudoEisenstein F φ with hE
  set E' : AdelicGL2 (𝓞 F) F → ℂ := pseudoEisenstein F ψ with hE'
  have hEc : Continuous E :=
    AutomorphicForm.continuous_pseudoEisenstein_of_isInducedSection_of_re_gt_half F hαm μ ν hμ hν s hs φ hφ hφc
  have hE'c : Continuous E' :=
    AutomorphicForm.continuous_pseudoEisenstein_of_isInducedSection_of_re_gt_half F hαm μ' ν' hμ' hν' s' hs' ψ hψ
      hψc
  have hφB := section_borel_invariant αm hαm hprin hμF hνF s hφ
  have hψB := section_borel_invariant αm hαm hprin hμ'F hν'F s' hψ
  have hEG : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), E (globalPoints (𝓞 F) F γ * g) = E g := by
    intro γ g
    have hsum := (AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hαm μ ν hμ hν s hs φ
      hφ hφc g).of_norm
    exact (AutomorphicForm.pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable F φ hφB g
      hsum γ).2
  have hE'G : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), E' (globalPoints (𝓞 F) F γ * g) = E' g := by
    intro γ g
    have hsum := (AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hαm μ' ν' hμ' hν' s' hs'
      ψ hψ hψc g).of_norm
    exact (AutomorphicForm.pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable F ψ hψB g
      hsum γ).2
  have hL2 : ∀ T : ℝ, MemLp (Λ T E) 2 (Haar.restrict Φ₀) := fun T =>
    AutomorphicForm.memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain F α β hα hαβ ∅ hαm μ ν
      hμ hν s hs φ hφ hφc hφK hφf T
  have hL2' : ∀ T : ℝ, MemLp (Λ T E') 2 (Haar.restrict Φ₀) := fun T =>
    AutomorphicForm.memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain F α β hα hαβ ∅ hαm μ' ν'
      hμ' hν' s' hs' ψ hψ hψc hψK hψf T
  have hprod : ∀ T : ℝ, IntegrableOn (fun x => Λ T E x * conj (Λ T E' x)) Φ₀ Haar := fun T =>
    (hL2 T).integrable_mul (memLp_conj (hL2' T))
  have hsq : IntegrableOn (fun g => ‖Λ R₁ E g‖ ^ 2) Φ₀ Haar :=
    (memLp_two_iff_integrable_sq_norm (hL2 R₁).1).1 (hL2 R₁)
  have hsq' : IntegrableOn (fun g => ‖Λ R₁ E' g‖ ^ 2) Φ₀ Haar :=
    (memLp_two_iff_integrable_sq_norm (hL2' R₁).1).1 (hL2' R₁)
  refine ⟨hprod R, hprod R', ?_⟩

  have hinc := hR₁ E E' hEc hE'c hEG hE'G hsq hsq' R R' hR hRR'
  rw [peterssonIntegral_zero, peterssonIntegral_zero] at hinc

  replace hinc :
      (∫ x in Φ₀, AutomorphicForm.lambdaT νb (fun t => AutomorphicForm.unipotentGL2 t) H (Real.exp R') E x *
          conj (AutomorphicForm.lambdaT νb (fun t => AutomorphicForm.unipotentGL2 t) H (Real.exp R') E' x) ∂Haar) -
        (∫ x in Φ₀, AutomorphicForm.lambdaT νb (fun t => AutomorphicForm.unipotentGL2 t) H (Real.exp R) E x *
          conj (AutomorphicForm.lambdaT νb (fun t => AutomorphicForm.unipotentGL2 t) H (Real.exp R) E' x) ∂Haar) = _ :=
    hinc

  set φ₂ : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    vC⁻¹ * AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g with hφ₂
  set ψ₂ : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    vC⁻¹ * AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g with hψ₂
  have hCTφ : ∀ g, AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E g = φ g + φ₂ g :=
    fun g => AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hαm μ ν hμ hν
      s hs φ hφ hφc g
  have hCTψ : ∀ g, AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E' g = ψ g + ψ₂ g :=
    fun g => AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hαm μ' ν' hμ'
      hν' s' hs' ψ hψ hψc g

  obtain ⟨hMφI, hMφc⟩ := AutomorphicForm.isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half F
    hαm μ ν hμ hν s hs φ hφ hφc
  obtain ⟨hMψI, hMψc⟩ := AutomorphicForm.isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half F
    hαm μ' ν' hμ' hν' s' hs' ψ hψ hψc
  have hφ₂I : IsInducedSection (𝓞 F) F (etaFst ν αm hαm (-s)) (etaSnd μ αm hαm (-s)) φ₂ :=
    (inducedSectionSubmodule (etaFst ν αm hαm (-s)) (etaSnd μ αm hαm (-s))).smul_mem vC⁻¹ hMφI
  have hψ₂I : IsInducedSection (𝓞 F) F (etaFst ν' αm hαm (-s')) (etaSnd μ' αm hαm (-s')) ψ₂ :=
    (inducedSectionSubmodule (etaFst ν' αm hαm (-s')) (etaSnd μ' αm hαm (-s'))).smul_mem vC⁻¹ hMψI
  have hφ₂c : Continuous φ₂ := continuous_const.mul hMφc
  have hψ₂c : Continuous ψ₂ := continuous_const.mul hMψc

  have hφ₂' : ∀ g, vC⁻¹ * AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g = φ₂ g :=
    fun g => rfl
  have hψ₂' : ∀ g, vC⁻¹ * AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g = ψ₂ g :=
    fun g => rfl
  simp only [hφ₂', hψ₂']

  have h11 := AutomorphicForm.integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa F
    hαm cT hcTtop hcT D D hDm hDm hDF hDF μ ν μ' ν' hμ hν hμ' hν' hμF hνF hμ'F hν'F s s' φ ψ hφ hψ hφc hψc α β R R'
    hα
  have h12 := AutomorphicForm.integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa F
    hαm cT hcTtop hcT D D hDm hDm hDF hDF μ ν ν' μ' hμ hν hν' hμ' hμF hνF hν'F hμ'F s (-s') φ ψ₂ hφ hψ₂I hφc hψ₂c α β
    R R' hα
  have h21 := AutomorphicForm.integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa F
    hαm cT hcTtop hcT D D hDm hDm hDF hDF ν μ μ' ν' hν hμ hμ' hν' hνF hμF hμ'F hν'F (-s) s' φ₂ ψ hφ₂I hψ hφ₂c hψc α β
    R R' hα
  have h22 := AutomorphicForm.integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa F
    hαm cT hcTtop hcT D D hDm hDm hDF hDF ν μ ν' μ' hν hμ hν' hμ' hνF hμF hν'F hμ'F (-s) (-s') φ₂ ψ₂ hφ₂I hψ₂I hφ₂c
    hψ₂c α β R R' hα
  obtain ⟨hi11, hv11⟩ := h11
  obtain ⟨hi12, hv12⟩ := h12
  obtain ⟨hi21, hv21⟩ := h21
  obtain ⟨hi22, hv22⟩ := h22

  set m : Measure (RationalTorusUnipotentQuotient F) := rationalTorusUnipotentQuotientMeasure F with hm
  set f11 : RationalTorusUnipotentQuotient F → ℂ := fun q =>
    X0.indicator (fun _ => (1 : ℂ)) q.out *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
      (φ q.out * conj (ψ q.out)) with hf11
  set f12 : RationalTorusUnipotentQuotient F → ℂ := fun q =>
    X0.indicator (fun _ => (1 : ℂ)) q.out *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
      (φ q.out * conj (ψ₂ q.out)) with hf12
  set f21 : RationalTorusUnipotentQuotient F → ℂ := fun q =>
    X0.indicator (fun _ => (1 : ℂ)) q.out *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
      (φ₂ q.out * conj (ψ q.out)) with hf21
  set f22 : RationalTorusUnipotentQuotient F → ℂ := fun q =>
    X0.indicator (fun _ => (1 : ℂ)) q.out *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
      (φ₂ q.out * conj (ψ₂ q.out)) with hf22
  have hI11i : Integrable f11 m := hi11
  have hI12i : Integrable f12 m := hi12
  have hI21i : Integrable f21 m := hi21
  have hI22i : Integrable f22 m := hi22
  have hsplit : (∫ q : RationalTorusUnipotentQuotient F,
        X0.indicator (fun _ => (1 : ℂ)) q.out *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
          (AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E q.out *
            conj (AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E' q.out)) ∂m)
      = (∫ q, f11 q ∂m) + (∫ q, f12 q ∂m) + (∫ q, f21 q ∂m) + (∫ q, f22 q ∂m) := by
    calc (∫ q : RationalTorusUnipotentQuotient F,
          X0.indicator (fun _ => (1 : ℂ)) q.out *
            (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
            (AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E q.out *
              conj (AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E' q.out)) ∂m)
        = ∫ q, (f11 q + f12 q + f21 q + f22 q) ∂m := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
          simp only [hf11, hf12, hf21, hf22, hCTφ, hCTψ, map_add]
          ring
      _ = (∫ q, (f11 q + f12 q + f21 q) ∂m) + ∫ q, f22 q ∂m :=
          integral_add ((hI11i.add hI12i).add hI21i) hI22i
      _ = (∫ q, (f11 q + f12 q) ∂m) + (∫ q, f21 q ∂m) + ∫ q, f22 q ∂m := by
          congr 1
          exact integral_add (hI11i.add hI12i) hI21i
      _ = (∫ q, f11 q ∂m) + (∫ q, f12 q ∂m) + (∫ q, f21 q ∂m) + ∫ q, f22 q ∂m := by
          congr 2
          exact integral_add hI11i hI12i
  have hv11' : ∫ q, f11 q ∂m = _ := hv11
  have hv12' : ∫ q, f12 q ∂m = _ := hv12
  have hv21' : ∫ q, f21 q ∂m = _ := hv21
  have hv22' : ∫ q, f22 q ∂m = _ := hv22

  set X : ℂ := s + conj s' with hX
  set Y : ℂ := s - conj s' with hY
  have hXre : 1 < X.re := by
    simp only [hX, Complex.add_re, Complex.conj_re]; linarith
  have hX0 : X ≠ 0 := fun h => by rw [h, Complex.zero_re] at hXre; linarith
  have hnX0 : -X ≠ 0 := neg_ne_zero.2 hX0
  have hnegX : -s + conj (-s') = -X := by rw [map_neg, hX]; ring
  have hsY : s + conj (-s') = Y := by rw [map_neg, hY]; ring
  have hsY' : -s + conj s' = -Y := by rw [hY]; ring
  have LB := fun {κ₁ κ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hκ₁ : IsUnitaryChar (𝓞 F) F κ₁)
      (hκ₂ : IsUnitaryChar (𝓞 F) F κ₂) (a b : ℂ) (hW : a + conj b ≠ 0) =>
    like_band F αm hαm hαI D hDm α β Cs hCstop hCs Cn hCnD hκ₁ hκ₂ a b hW R R' hRR'
  have DB := fun {κ₁ κ₂ κ₁' κ₂' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
      (hκ₁' : IsUnitaryChar (𝓞 F) F κ₁') (hκ₂' : IsUnitaryChar (𝓞 F) F κ₂')
      (hκ₁F : IsIdeleClassChar (𝓞 F) F κ₁) (hκ₂F : IsIdeleClassChar (𝓞 F) F κ₂)
      (hκ₁'F : IsIdeleClassChar (𝓞 F) F κ₁') (hκ₂'F : IsIdeleClassChar (𝓞 F) F κ₂')
      (hex : ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, κ₁' z ≠ κ₁ z ∨ κ₂' z ≠ κ₂ z) (a b : ℂ) =>
    dead_band F αm hαm hαI D hDm hDF α β hκ₁' hκ₂' hκ₁F hκ₂F hκ₁'F hκ₂'F hex a b R R'
  have hexp1 : Complex.exp ((R' : ℂ) * (-X)) = Complex.exp (-((R' : ℂ) * X)) := by rw [mul_neg]
  have hexp2 : Complex.exp ((R : ℂ) * (-X)) = Complex.exp (-((R : ℂ) * X)) := by rw [mul_neg]
  have hexp3 : Complex.exp ((R' : ℂ) * (-Y)) = Complex.exp (-((R' : ℂ) * Y)) := by rw [mul_neg]
  have hexp4 : Complex.exp ((R : ℂ) * (-Y)) = Complex.exp (-((R : ℂ) * Y)) := by rw [mul_neg]
  refine ⟨fun h1 h2 hμν hne => ?_, fun h1 h2 hμν => ?_, fun h1 h2 hμν hne => ?_, fun hD1 hD2 => ?_⟩
  ·
    obtain rfl : μ = μ' := h1.symm
    obtain rfl : ν = ν' := h2.symm
    subst hμν
    have hY0 : Y ≠ 0 := sub_ne_zero.2 hne
    have hnY0 : -Y ≠ 0 := neg_ne_zero.2 hY0
    have hI11 := LB hμ hμ s s' hX0
    have hI22 := LB hμ hμ (-s) (-s') (by rw [hnegX]; exact hnX0)
    have hI12 := LB hμ hμ s (-s') (by rw [hsY]; exact hY0)
    have hI21 := LB hμ hμ (-s) s' (by rw [hsY']; exact hnY0)
    rw [← hX] at hI11
    rw [hnegX] at hI22
    rw [hsY] at hI12
    rw [hsY'] at hI21
    refine hinc.trans ?_
    rw [hsplit, hv11', hv12', hv21', hv22', hI11, hI22, hI12, hI21, hexp1, hexp2, hexp3, hexp4]

    push_cast
    field_simp
    ring
  ·
    obtain rfl : μ = μ' := h1.symm
    obtain rfl : ν = ν' := h2.symm
    have hexBC : ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, ν z ≠ μ z ∨ μ z ≠ ν z := by
      obtain ⟨z, hz, hne⟩ := hμν
      exact ⟨z, hz, Or.inr hne⟩
    have hexCB : ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z ∨ ν z ≠ μ z := by
      obtain ⟨z, hz, hne⟩ := hμν
      exact ⟨z, hz, Or.inl hne⟩
    have hI11 := LB hμ hν s s' hX0
    have hI22 := LB hν hμ (-s) (-s') (by rw [hnegX]; exact hnX0)
    have hI12 := DB (κ₁ := μ) (κ₂ := ν) hν hμ hμF hνF hνF hμF hexBC s (-s')
    have hI21 := DB (κ₁ := ν) (κ₂ := μ) hμ hν hνF hμF hμF hνF hexCB (-s) s'
    rw [← hX] at hI11
    rw [hnegX] at hI22
    refine hinc.trans ?_
    rw [hsplit, hv11', hv12', hv21', hv22', hI11, hI22, hI12, hI21, hexp1, hexp2]

    simp only [mul_zero, add_zero]
    push_cast
    field_simp
    ring
  ·
    obtain rfl : ν = μ' := h1.symm
    obtain rfl : μ = ν' := h2.symm
    have hY0 : Y ≠ 0 := sub_ne_zero.2 hne
    have hnY0 : -Y ≠ 0 := neg_ne_zero.2 hY0
    have hexBC : ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, ν z ≠ μ z ∨ μ z ≠ ν z := by
      obtain ⟨z, hz, hne⟩ := hμν
      exact ⟨z, hz, Or.inr hne⟩
    have hexCB : ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z ∨ ν z ≠ μ z := by
      obtain ⟨z, hz, hne⟩ := hμν
      exact ⟨z, hz, Or.inl hne⟩
    have hI11 := DB (κ₁ := μ) (κ₂ := ν) hν hμ hμF hνF hνF hμF hexBC s s'
    have hI22 := DB (κ₁ := ν) (κ₂ := μ) hμ hν hνF hμF hμF hνF hexCB (-s) (-s')
    have hI12 := LB hμ hν s (-s') (by rw [hsY]; exact hY0)
    have hI21 := LB hν hμ (-s) s' (by rw [hsY']; exact hnY0)
    rw [hsY] at hI12
    rw [hsY'] at hI21
    refine hinc.trans ?_
    rw [hsplit, hv11', hv12', hv21', hv22', hI11, hI22, hI12, hI21, hexp3, hexp4]

    simp only [mul_zero, zero_add, add_zero]
    push_cast
    field_simp
    ring
  ·
    have hD1' : ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, ν' z ≠ ν z ∨ μ' z ≠ μ z := by
      obtain ⟨z, hz, h⟩ := hD1
      exact ⟨z, hz, h.symm⟩
    have hD2' : ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, ν' z ≠ μ z ∨ μ' z ≠ ν z := by
      obtain ⟨z, hz, h⟩ := hD2
      exact ⟨z, hz, h.symm⟩
    have hI11 := DB (κ₁ := μ) (κ₂ := ν) hμ' hν' hμF hνF hμ'F hν'F hD1 s s'
    have hI22 := DB (κ₁ := ν) (κ₂ := μ) hν' hμ' hνF hμF hν'F hμ'F hD1' (-s) (-s')
    have hI12 := DB (κ₁ := μ) (κ₂ := ν) hν' hμ' hμF hνF hν'F hμ'F hD2' s (-s')
    have hI21 := DB (κ₁ := ν) (κ₂ := μ) hμ' hν' hνF hμF hμ'F hν'F hD2 (-s) s'
    refine hinc.trans ?_
    rw [hsplit, hv11', hv12', hv21', hv22', hI11, hI22, hI12, hI21]
    simp only [mul_zero, add_zero]

end S_AutomorphicForm_exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_and_sub_eq_cross_sub_and_sub_eq_zero_two_pairs_slab
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_and_sub_eq_cross_sub_and_sub_eq_zero_two_pairs_slab (solution)
