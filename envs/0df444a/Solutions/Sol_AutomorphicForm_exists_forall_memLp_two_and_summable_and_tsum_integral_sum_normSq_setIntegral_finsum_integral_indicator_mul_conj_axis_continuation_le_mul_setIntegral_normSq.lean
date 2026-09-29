-- Prove2me | solution 1 for AutomorphicForm.exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/89f560fe-4fbe-5c80-97c5-b8007bce72db

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_AutomorphicForm_exists_matched_paleyWiener_sum_integral_sum_conj_inner_mul_eq_sum_integral_sum_conj_integral_mul_cexp_mul_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport
import Theorems.Thm_MeasureTheory_memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le
import Theorems.Thm_MeasureTheory_exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp
import Theorems.Thm_AutomorphicForm_continuous_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight
import Theorems.Thm_AutomorphicForm_exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_exists_forall_mem_canonicalTruncationDomain_finsum_integral_indicator_eq_zero_of_lt_adelicHeight
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
import Theorems.Thm_MeasureTheory_norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply"
p2m_attr_erase "simp" "AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.iotaZsqrtdNegTwo_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply"
p2m_attr_erase "simp" "NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped ContDiff

namespace L2Kit

section Aux

theorem aux_norm_mul_conj_le (z w : ℂ) : ‖z * conj w‖ ≤ (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

theorem aux_conj_mul_conj (z w : ℂ) : conj (z * conj w) = w * conj z := by
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem aux_norm_sub_sq_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  nlinarith [mul_nonneg (norm_nonneg (a - b)) (sub_nonneg.2 (norm_sub_le a b)),
    mul_self_nonneg (‖a‖ + ‖b‖ - ‖a - b‖), sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem aux_norm_add_sq_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  nlinarith [mul_nonneg (norm_nonneg (a + b)) (sub_nonneg.2 (norm_add_le a b)),
    mul_self_nonneg (‖a‖ + ‖b‖ - ‖a + b‖), sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem aux_cs {a b u : ℝ} (hb : 0 ≤ b) (hu : 0 ≤ u)
    (h : ∀ t : ℝ, 0 ≤ a - 2 * t * u + t ^ 2 * u * b) : u ≤ a * b := by
  rcases hb.lt_or_eq with hb' | hb'
  · have h1 := h b⁻¹
    have h2 : a - 2 * b⁻¹ * u + b⁻¹ ^ 2 * u * b = a - b⁻¹ * u := by
      field_simp
      ring
    rw [h2] at h1
    have h3 : b⁻¹ * u ≤ a := by linarith
    calc u = b * (b⁻¹ * u) := by field_simp
      _ ≤ b * a := mul_le_mul_of_nonneg_left h3 hb'.le
      _ = a * b := mul_comm _ _
  · subst hb'
    by_contra hcon
    have hu' : 0 < u := by
      rcases hu.lt_or_eq with h' | h'
      · exact h'
      · exact absurd (by rw [← h']; simp) hcon
    have h1 := h ((a + 1) / (2 * u))
    have h2 : 2 * ((a + 1) / (2 * u)) * u = a + 1 := by
      field_simp
    rw [h2] at h1
    simp at h1
    linarith

theorem aux_cs_finish {a b : ℝ} {z : ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 ≤ ((a : ℂ) - conj ((t : ℂ) * z) * z - (t : ℂ) * z * conj z
      + (t : ℂ) * z * conj ((t : ℂ) * z) * (b : ℂ)).re) :
    ‖z‖ ≤ Real.sqrt a * Real.sqrt b := by
  have hz : z * conj z = ((‖z‖ : ℝ) : ℂ) ^ 2 := RCLike.mul_conj z
  have key : ∀ t : ℝ, 0 ≤ a - 2 * t * ‖z‖ ^ 2 + t ^ 2 * ‖z‖ ^ 2 * b := by
    intro t
    have hc : ((a : ℂ) - conj ((t : ℂ) * z) * z - (t : ℂ) * z * conj z
        + (t : ℂ) * z * conj ((t : ℂ) * z) * (b : ℂ))
        = ((a - 2 * t * ‖z‖ ^ 2 + t ^ 2 * ‖z‖ ^ 2 * b : ℝ) : ℂ) := by
      simp only [map_mul, Complex.conj_ofReal]
      push_cast
      rw [← hz]
      ring
    have := h t
    rwa [hc, Complex.ofReal_re] at this
  have hsq : ‖z‖ ^ 2 ≤ a * b := aux_cs hb (sq_nonneg _) key
  rw [← Real.sqrt_mul ha]
  exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg ha hb)).2 hsq

variable {α : Type} [MeasurableSpace α] {μ : Measure α}

theorem aux_memLp_conj {g : α → ℂ} (hg : MemLp g 2 μ) : MemLp (fun x => conj (g x)) 2 μ :=
  MemLp.of_le hg (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => (Complex.norm_conj _).le)

theorem aux_integrable_mul_conj {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => f x * conj (g x)) μ := by
  have h := hf.integrable_mul (aux_memLp_conj hg)
  exact h

theorem aux_integrable_norm_sq {f : α → ℂ} (hf : MemLp f 2 μ) :
    Integrable (fun x => ‖f x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf

theorem aux_integral_mul_conj_self (f : α → ℂ) :
    (∫ x, f x * conj (f x) ∂μ) = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact integral_complex_ofReal

theorem aux_integral_mul_conj_symm (f g : α → ℂ) :
    (∫ x, g x * conj (f x) ∂μ) = conj (∫ x, f x * conj (g x) ∂μ) := by
  rw [← integral_conj]
  congr 1
  funext x
  rw [aux_conj_mul_conj]

theorem aux_integral_const_mul_mul_conj (c : ℂ) (f g : α → ℂ) :
    (∫ x, c * f x * conj (g x) ∂μ) = c * ∫ x, f x * conj (g x) ∂μ := by
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

theorem aux_integral_mul_conj_const_mul (c : ℂ) (f g : α → ℂ) :
    (∫ x, f x * conj (c * g x) ∂μ) = conj c * ∫ x, f x * conj (g x) ∂μ := by
  have : ∀ x, f x * conj (c * g x) = conj c * (f x * conj (g x)) := fun x => by
    rw [map_mul]; ring
  simp_rw [this]
  exact integral_const_mul _ _

end Aux

section A
variable {ι : Type} {n : ι → ℕ}

structure MemH (F : (e : ι) → Fin (n e) → ℝ → ℂ) : Prop where
  memLp : ∀ (e : ι) (j : Fin (n e)), MemLp (F e j) 2
  summable : Summable (fun e : ι => ∫ t : ℝ, ∑ j : Fin (n e), ‖F e j t‖ ^ 2)

noncomputable def N (F : (e : ι) → Fin (n e) → ℝ → ℂ) : ℝ :=
  ∑' e : ι, ∫ t : ℝ, ∑ j : Fin (n e), ‖F e j t‖ ^ 2

noncomputable def P (F G : (e : ι) → Fin (n e) → ℝ → ℂ) : ℂ :=
  ∑' e : ι, ∫ t : ℝ, ∑ j : Fin (n e), F e j t * conj (G e j t)

variable {F G F' G' : (e : ι) → Fin (n e) → ℝ → ℂ}

theorem MemH.integrable_sum_norm_sq (hF : MemH F) (e : ι) :
    Integrable (fun t : ℝ => ∑ j : Fin (n e), ‖F e j t‖ ^ 2) :=
  integrable_finsetSum Finset.univ fun j _ => aux_integrable_norm_sq (hF.memLp e j)

theorem aux_summable_nonneg_le (hF : MemH F) (hG : MemH G) {g : ι → ℝ} (hg0 : ∀ e, 0 ≤ g e)
    (hle : ∀ e, g e ≤ 2 * ((∫ t : ℝ, ∑ j : Fin (n e), ‖F e j t‖ ^ 2) + ∫ t : ℝ, ∑ j : Fin (n e), ‖G e j t‖ ^ 2)) :
    Summable g :=
  Summable.of_nonneg_of_le hg0 hle ((hF.summable.add hG.summable).mul_left 2)

theorem MemH.sub (hF : MemH F) (hG : MemH G) : MemH (fun e j t => F e j t - G e j t) := by
  have hmem : ∀ (e : ι) (j : Fin (n e)), MemLp (fun t => F e j t - G e j t) 2 :=
    fun e j => (hF.memLp e j).sub (hG.memLp e j)
  refine ⟨hmem, ?_⟩
  refine aux_summable_nonneg_le hF hG
    (fun e => integral_nonneg fun t => Finset.sum_nonneg fun j _ => by positivity) fun e => ?_
  have hint : Integrable (fun t : ℝ => ∑ j : Fin (n e), ‖F e j t - G e j t‖ ^ 2) :=
    integrable_finsetSum Finset.univ fun j _ => aux_integrable_norm_sq (hmem e j)
  calc (∫ t : ℝ, ∑ j : Fin (n e), ‖F e j t - G e j t‖ ^ 2)
      ≤ ∫ t : ℝ, 2 * (∑ j : Fin (n e), ‖F e j t‖ ^ 2 + ∑ j : Fin (n e), ‖G e j t‖ ^ 2) := by
        refine integral_mono hint
          (((hF.integrable_sum_norm_sq e).add (hG.integrable_sum_norm_sq e)).const_mul 2) fun t => ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => aux_norm_sub_sq_le _ _
    _ = 2 * ((∫ t : ℝ, ∑ j : Fin (n e), ‖F e j t‖ ^ 2) + ∫ t : ℝ, ∑ j : Fin (n e), ‖G e j t‖ ^ 2) := by
        rw [integral_const_mul, integral_add (hF.integrable_sum_norm_sq e) (hG.integrable_sum_norm_sq e)]

theorem MemH.add (hF : MemH F) (hG : MemH G) : MemH (fun e j t => F e j t + G e j t) := by
  have hmem : ∀ (e : ι) (j : Fin (n e)), MemLp (fun t => F e j t + G e j t) 2 :=
    fun e j => (hF.memLp e j).add (hG.memLp e j)
  refine ⟨hmem, ?_⟩
  refine aux_summable_nonneg_le hF hG
    (fun e => integral_nonneg fun t => Finset.sum_nonneg fun j _ => by positivity) fun e => ?_
  have hint : Integrable (fun t : ℝ => ∑ j : Fin (n e), ‖F e j t + G e j t‖ ^ 2) :=
    integrable_finsetSum Finset.univ fun j _ => aux_integrable_norm_sq (hmem e j)
  calc (∫ t : ℝ, ∑ j : Fin (n e), ‖F e j t + G e j t‖ ^ 2)
      ≤ ∫ t : ℝ, 2 * (∑ j : Fin (n e), ‖F e j t‖ ^ 2 + ∑ j : Fin (n e), ‖G e j t‖ ^ 2) := by
        refine integral_mono hint
          (((hF.integrable_sum_norm_sq e).add (hG.integrable_sum_norm_sq e)).const_mul 2) fun t => ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => aux_norm_add_sq_le _ _
    _ = 2 * ((∫ t : ℝ, ∑ j : Fin (n e), ‖F e j t‖ ^ 2) + ∫ t : ℝ, ∑ j : Fin (n e), ‖G e j t‖ ^ 2) := by
        rw [integral_const_mul, integral_add (hF.integrable_sum_norm_sq e) (hG.integrable_sum_norm_sq e)]

theorem MemH.neg (hF : MemH F) : MemH (fun e j t => -F e j t) := by
  refine ⟨fun e j => (hF.memLp e j).neg, ?_⟩
  simpa only [norm_neg] using hF.summable

theorem MemH.const_mul (hF : MemH F) (c : ℂ) : MemH (fun e j t => c * F e j t) := by
  refine ⟨fun e j => (hF.memLp e j).const_mul c, ?_⟩
  have : (fun e : ι => ∫ t : ℝ, ∑ j : Fin (n e), ‖c * F e j t‖ ^ 2)
      = fun e : ι => ‖c‖ ^ 2 * ∫ t : ℝ, ∑ j : Fin (n e), ‖F e j t‖ ^ 2 := by
    funext e
    simp_rw [norm_mul, mul_pow, ← Finset.mul_sum]
    exact integral_const_mul _ _
  rw [this]
  exact hF.summable.mul_left _

theorem N_nonneg (F : (e : ι) → Fin (n e) → ℝ → ℂ) : 0 ≤ N F :=
  tsum_nonneg fun e => integral_nonneg fun t => Finset.sum_nonneg fun j _ => by positivity

theorem MemH.integrable_inner (hF : MemH F) (hG : MemH G) (e : ι) :
    Integrable (fun t : ℝ => ∑ j : Fin (n e), F e j t * conj (G e j t)) :=
  integrable_finsetSum Finset.univ fun j _ => aux_integrable_mul_conj (hF.memLp e j) (hG.memLp e j)

theorem MemH.norm_integral_inner_le (hF : MemH F) (hG : MemH G) (e : ι) :
    ‖∫ t : ℝ, ∑ j : Fin (n e), F e j t * conj (G e j t)‖
      ≤ ((∫ t : ℝ, ∑ j : Fin (n e), ‖F e j t‖ ^ 2) + ∫ t : ℝ, ∑ j : Fin (n e), ‖G e j t‖ ^ 2) / 2 := by
  calc ‖∫ t : ℝ, ∑ j : Fin (n e), F e j t * conj (G e j t)‖
      ≤ ∫ t : ℝ, ‖∑ j : Fin (n e), F e j t * conj (G e j t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (∑ j : Fin (n e), ‖F e j t‖ ^ 2 + ∑ j : Fin (n e), ‖G e j t‖ ^ 2) / 2 := by
        refine integral_mono (hF.integrable_inner hG e).norm
          (((hF.integrable_sum_norm_sq e).add (hG.integrable_sum_norm_sq e)).div_const 2) fun t => ?_
        refine (norm_sum_le _ _).trans ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_le_sum fun j _ => aux_norm_mul_conj_le _ _
    _ = ((∫ t : ℝ, ∑ j : Fin (n e), ‖F e j t‖ ^ 2) + ∫ t : ℝ, ∑ j : Fin (n e), ‖G e j t‖ ^ 2) / 2 := by
        rw [integral_div, integral_add (hF.integrable_sum_norm_sq e) (hG.integrable_sum_norm_sq e)]

theorem MemH.summable_norm_inner (hF : MemH F) (hG : MemH G) :
    Summable (fun e : ι => ‖∫ t : ℝ, ∑ j : Fin (n e), F e j t * conj (G e j t)‖) :=
  Summable.of_nonneg_of_le (fun e => norm_nonneg _) (fun e => hF.norm_integral_inner_le hG e)
    ((hF.summable.add hG.summable).div_const 2)

theorem MemH.summable_inner (hF : MemH F) (hG : MemH G) :
    Summable (fun e : ι => ∫ t : ℝ, ∑ j : Fin (n e), F e j t * conj (G e j t)) :=
  (hF.summable_norm_inner hG).of_norm

theorem P_self (hF : MemH F) : P F F = (N F : ℂ) := by
  unfold P N
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun e => ?_
  rw [← integral_complex_ofReal]
  congr 1
  funext t
  push_cast
  exact Finset.sum_congr rfl fun j _ => RCLike.mul_conj _

theorem P_conj_symm (hF : MemH F) (hG : MemH G) : P G F = conj (P F G) := by
  unfold P
  rw [Complex.conj_tsum]
  refine tsum_congr fun e => ?_
  rw [← integral_conj]
  congr 1
  funext t
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => (aux_conj_mul_conj _ _).symm

theorem P_const_mul_left (c : ℂ) (F G : (e : ι) → Fin (n e) → ℝ → ℂ) :
    P (fun e j t => c * F e j t) G = c * P F G := by
  unfold P
  rw [← tsum_mul_left]
  refine tsum_congr fun e => ?_
  rw [← integral_const_mul]
  congr 1
  funext t
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem P_const_mul_right (c : ℂ) (F G : (e : ι) → Fin (n e) → ℝ → ℂ) :
    P F (fun e j t => c * G e j t) = conj c * P F G := by
  unfold P
  rw [← tsum_mul_left]
  refine tsum_congr fun e => ?_
  rw [← integral_const_mul]
  congr 1
  funext t
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; ring

theorem P_sub_left (hF : MemH F) (hF' : MemH F') (hG : MemH G) :
    P (fun e j t => F e j t - F' e j t) G = P F G - P F' G := by
  unfold P
  rw [← Summable.tsum_sub (hF.summable_inner hG) (hF'.summable_inner hG)]
  refine tsum_congr fun e => ?_
  rw [← integral_sub (hF.integrable_inner hG e) (hF'.integrable_inner hG e)]
  congr 1
  funext t
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem P_sub_right (hF : MemH F) (hG : MemH G) (hG' : MemH G') :
    P F (fun e j t => G e j t - G' e j t) = P F G - P F G' := by
  unfold P
  rw [← Summable.tsum_sub (hF.summable_inner hG) (hF.summable_inner hG')]
  refine tsum_congr fun e => ?_
  rw [← integral_sub (hF.integrable_inner hG e) (hF.integrable_inner hG' e)]
  congr 1
  funext t
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [map_sub]; ring

theorem P_add_left (hF : MemH F) (hF' : MemH F') (hG : MemH G) :
    P (fun e j t => F e j t + F' e j t) G = P F G + P F' G := by
  unfold P
  rw [← Summable.tsum_add (hF.summable_inner hG) (hF'.summable_inner hG)]
  refine tsum_congr fun e => ?_
  rw [← integral_add (hF.integrable_inner hG e) (hF'.integrable_inner hG e)]
  congr 1
  funext t
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem P_add_right (hF : MemH F) (hG : MemH G) (hG' : MemH G') :
    P F (fun e j t => G e j t + G' e j t) = P F G + P F G' := by
  unfold P
  rw [← Summable.tsum_add (hF.summable_inner hG) (hF.summable_inner hG')]
  refine tsum_congr fun e => ?_
  rw [← integral_add (hF.integrable_inner hG e) (hF.integrable_inner hG' e)]
  congr 1
  funext t
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [map_add]; ring

theorem aux_N_sub_const_mul (hF : MemH F) (hG : MemH G) (l : ℂ) :
    ((N (fun e j t => F e j t - l * G e j t) : ℝ) : ℂ)
      = (N F : ℂ) - conj l * P F G - l * conj (P F G) + l * conj l * (N G : ℂ) := by
  have hlG : MemH (fun e j t => l * G e j t) := hG.const_mul l
  have hD : MemH (fun e j t => F e j t - l * G e j t) := hF.sub hlG
  rw [← P_self hD, P_sub_left hF hlG hD, P_sub_right hF hF hlG, P_sub_right hlG hF hlG]
  simp only [P_const_mul_left, P_const_mul_right]
  rw [P_self hF, P_self hG, P_conj_symm hF hG]
  ring

theorem norm_P_le (hF : MemH F) (hG : MemH G) :
    ‖P F G‖ ≤ Real.sqrt (N F) * Real.sqrt (N G) := by
  refine aux_cs_finish (N_nonneg F) (N_nonneg G) fun t => ?_
  rw [← aux_N_sub_const_mul hF hG ((t : ℂ) * P F G), Complex.ofReal_re]
  exact N_nonneg _

theorem aux_N_add (hF : MemH F) (hG : MemH G) :
    N (fun e j t => F e j t + G e j t) = N F + 2 * (P F G).re + N G := by
  have h0 : N (fun e j t => F e j t + G e j t) = N (fun e j t => F e j t - (-1) * G e j t) := by
    congr 1
    funext e j t
    ring
  have h1 : ((N (fun e j t => F e j t - (-1) * G e j t) : ℝ) : ℂ)
      = (N F : ℂ) + P F G + conj (P F G) + (N G : ℂ) := by
    rw [aux_N_sub_const_mul hF hG (-1)]
    simp only [map_neg, map_one]
    ring
  have h2 := congrArg Complex.re h1
  simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re] at h2
  rw [h0, h2]
  ring

theorem sqrt_N_add_le (hF : MemH F) (hG : MemH G) :
    Real.sqrt (N (fun e j t => F e j t + G e j t)) ≤ Real.sqrt (N F) + Real.sqrt (N G) := by
  rw [Real.sqrt_le_left (by positivity), aux_N_add hF hG, add_sq, Real.sq_sqrt (N_nonneg F),
    Real.sq_sqrt (N_nonneg G)]
  have h1 := (Complex.re_le_norm (P F G)).trans (norm_P_le hF hG)
  nlinarith [h1, Real.sqrt_nonneg (N F), Real.sqrt_nonneg (N G)]

theorem sqrt_N_sub_le (hF : MemH F) (hG : MemH G) (hK : MemH G') :
    Real.sqrt (N (fun e j t => F e j t - G e j t))
      ≤ Real.sqrt (N (fun e j t => F e j t - G' e j t)) + Real.sqrt (N (fun e j t => G' e j t - G e j t)) := by
  have h0 : N (fun e j t => F e j t - G e j t)
      = N (fun e j t => (F e j t - G' e j t) + (G' e j t - G e j t)) := by
    congr 1
    funext e j t
    ring
  rw [h0]
  exact sqrt_N_add_le (hF.sub hK) (hK.sub hG)

theorem N_neg (F : (e : ι) → Fin (n e) → ℝ → ℂ) : N (fun e j t => -F e j t) = N F := by
  simp only [N, norm_neg]

theorem N_sub_eq_re_P (hF : MemH F) (hG : MemH G) :
    N (fun e j t => F e j t - G e j t)
      = (P (fun e j t => F e j t - G e j t) (fun e j t => F e j t - G e j t)).re := by
  rw [P_self (hF.sub hG), Complex.ofReal_re]

end A

section B

variable {α : Type} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}

theorem integrable_mul_conj (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => f x * conj (g x)) μ :=
  aux_integrable_mul_conj hf hg

theorem integral_norm_sq_eq (hf : MemLp f 2 μ) :
    (∫ x, f x * conj (f x) ∂μ) = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) :=
  aux_integral_mul_conj_self f

theorem integral_norm_sq_nonneg (f : α → ℂ) : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ :=
  integral_nonneg fun x => by positivity

theorem integral_sub_mul_conj (hf : MemLp f 2 μ) (hf' : MemLp g 2 μ) (h : α → ℂ) (hh : MemLp h 2 μ) :
    (∫ x, (f x - g x) * conj (h x) ∂μ) = (∫ x, f x * conj (h x) ∂μ) - ∫ x, g x * conj (h x) ∂μ := by
  rw [← integral_sub (aux_integrable_mul_conj hf hh) (aux_integrable_mul_conj hf' hh)]
  congr 1
  funext x
  ring

theorem integral_mul_conj_sub (h : α → ℂ) (hh : MemLp h 2 μ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, h x * conj (f x - g x) ∂μ) = (∫ x, h x * conj (f x) ∂μ) - ∫ x, h x * conj (g x) ∂μ := by
  rw [← integral_sub (aux_integrable_mul_conj hh hf) (aux_integrable_mul_conj hh hg)]
  congr 1
  funext x
  rw [map_sub]
  ring

theorem integral_mul_conj_real_smul (f g : α → ℂ) (c : ℝ) :
    (∫ x, f x * conj ((c : ℂ) * g x) ∂μ) = (c : ℂ) * ∫ x, f x * conj (g x) ∂μ := by
  rw [aux_integral_mul_conj_const_mul, Complex.conj_ofReal]

theorem aux_integral_norm_sq_sub_const_mul (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (l : ℂ) :
    ((∫ x, ‖f x - l * g x‖ ^ 2 ∂μ : ℝ) : ℂ)
      = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) - conj l * (∫ x, f x * conj (g x) ∂μ)
        - l * conj (∫ x, f x * conj (g x) ∂μ) + l * conj l * ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hlg : MemLp (fun x => l * g x) 2 μ := hg.const_mul l
  have hD : MemLp (fun x => f x - l * g x) 2 μ := hf.sub hlg
  rw [← integral_norm_sq_eq hD, integral_sub_mul_conj hf hlg _ hD, integral_mul_conj_sub f hf hf hlg,
    integral_mul_conj_sub (fun x => l * g x) hlg hf hlg]
  simp only [aux_integral_const_mul_mul_conj, aux_integral_mul_conj_const_mul]
  rw [integral_norm_sq_eq hf, integral_norm_sq_eq hg, aux_integral_mul_conj_symm f g]
  ring

theorem norm_integral_mul_conj_le (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * conj (g x) ∂μ‖ ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  refine aux_cs_finish (integral_norm_sq_nonneg f) (integral_norm_sq_nonneg g) fun t => ?_
  rw [← aux_integral_norm_sq_sub_const_mul hf hg ((t : ℂ) * ∫ x, f x * conj (g x) ∂μ),
    Complex.ofReal_re]
  exact integral_norm_sq_nonneg _

theorem toReal_eLpNorm_eq_sqrt (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun a => Real.rpow_nonneg (norm_nonneg _) _) _),
    Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]

end B

section C

variable {α : Type} [MeasurableSpace α] {μ : Measure α}

theorem integral_mul_conj_eq_zero_of_forall_approx {x y : α → ℂ} (hx : MemLp x 2 μ) (hy : MemLp y 2 μ)
    (h : ∀ ε > (0:ℝ), ∃ r : α → ℂ, MemLp r 2 μ ∧ (∫ a, x a * conj (r a) ∂μ) = 0 ∧
      eLpNorm (y - r) 2 μ < ENNReal.ofReal ε) :
    (∫ a, x a * conj (y a) ∂μ) = 0 := by
  set A : ℝ := Real.sqrt (∫ a, ‖x a‖ ^ 2 ∂μ) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have key : ∀ ε > (0:ℝ), ‖∫ a, x a * conj (y a) ∂μ‖ ≤ A * ε := by
    intro ε hε
    obtain ⟨r, hr, hxr, hyr⟩ := h ε hε
    have hyr' : MemLp (fun a => y a - r a) 2 μ := hy.sub hr
    have hlt : eLpNorm (fun a => y a - r a) 2 μ < ENNReal.ofReal ε := hyr
    have h1 : (∫ a, x a * conj (y a) ∂μ) = ∫ a, x a * conj (y a - r a) ∂μ := by
      rw [integral_mul_conj_sub x hx hy hr, hxr, sub_zero]
    rw [h1]
    refine (norm_integral_mul_conj_le hx hyr').trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hA0
    rw [← toReal_eLpNorm_eq_sqrt hyr']
    exact (ENNReal.toReal_lt_of_lt_ofReal hlt).le
  by_contra hne
  have hI : 0 < ‖∫ a, x a * conj (y a) ∂μ‖ := norm_pos_iff.2 hne
  have h2 := key (‖∫ a, x a * conj (y a) ∂μ‖ / (A + 1)) (by positivity)
  have h3 : A / (A + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have h4 : A * (‖∫ a, x a * conj (y a) ∂μ‖ / (A + 1))
      = ‖∫ a, x a * conj (y a) ∂μ‖ * (A / (A + 1)) := by ring
  have h5 := mul_lt_mul_of_pos_left h3 hI
  linarith

theorem integral_mul_conj_eq_zero_of_forall_approx' {x y : α → ℂ} (hx : MemLp x 2 μ) (hy : MemLp y 2 μ)
    (h : ∀ ε > (0:ℝ), ∃ r : α → ℂ, MemLp r 2 μ ∧ (∫ a, r a * conj (x a) ∂μ) = 0 ∧
      eLpNorm (y - r) 2 μ < ENNReal.ofReal ε) :
    (∫ a, y a * conj (x a) ∂μ) = 0 := by
  rw [aux_integral_mul_conj_symm x y, integral_mul_conj_eq_zero_of_forall_approx hx hy ?_, map_zero]
  intro ε hε
  obtain ⟨r, hr, h0, hε'⟩ := h ε hε
  refine ⟨r, hr, ?_, hε'⟩
  rw [aux_integral_mul_conj_symm x r] at h0
  have := congrArg (starRingEnd ℂ) h0
  simpa using this

end C

section D

theorem le_of_forall_pos_sq_le {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s)
    (h : ∀ δ : ℝ, 0 < δ → x ^ 2 ≤ x * δ + s * (x + δ)) : x ≤ s := by
  by_contra hxs
  rw [not_le] at hxs
  have h1 := h ((x - s) / 4) (by linarith)
  nlinarith [mul_pos (sub_pos.2 hxs) (by linarith : (0:ℝ) < 3 * x - s)]
end D

end L2Kit

namespace FIKit

theorem aux_norm_cexp (t x : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ = 1 := by
  rw [show (t : ℂ) * Complex.I * (x : ℂ) = ((t * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem aux_continuous_integrand (h : ℝ → ℂ) (hh : Continuous h) (t : ℝ) :
    Continuous (fun x : ℝ => h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) :=
  hh.mul (Continuous.cexp (continuous_const.mul Complex.continuous_ofReal))

theorem aux_integrable_one_add_abs_rpow_neg_two (c : ℝ) :
    Integrable (fun t : ℝ => c * (1 + |t|) ^ (-(2:ℝ))) := by
  have hi := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  simpa only [Real.norm_eq_abs] using hi.const_mul c

theorem continuous_FI (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    Continuous (fun t : ℝ => ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) := by
  refine continuous_of_dominated (bound := fun x => ‖h x‖) ?_ ?_ ?_ ?_
  · intro t
    exact (aux_continuous_integrand h hh.continuous t).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall fun x => by rw [norm_mul, aux_norm_cexp, mul_one]
  · exact hh.continuous.norm.integrable_of_hasCompactSupport hc.norm
  · exact Filter.Eventually.of_forall fun x =>
      continuous_const.mul (Continuous.cexp ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const))

theorem exists_norm_FI_le (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ ≤ C * (1 + |t|) ^ (-(N : ℝ)) := by
  refine ⟨2 ^ N * ((∫ u : ℝ, ‖h u‖) + ∫ u : ℝ, ‖iteratedDeriv N h u‖),
    mul_nonneg (pow_nonneg (by norm_num) N)
      (add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)), fun t => ?_⟩
  have hN : ContDiff ℝ N h := hh.of_le (by exact_mod_cast le_top)
  have key := MeasureTheory.norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport
    N h hN hc t
  have e : ∀ x : ℝ, (t : ℂ) * Complex.I * (x : ℂ) = Complex.I * (t : ℂ) * (x : ℂ) := fun x => by ring
  simp_rw [e]
  exact key

theorem integrable_conj_FI_mul (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (Θ : ℝ → ℂ) (hΘ : Continuous Θ) (hΘg : ∃ (A : ℝ) (k : ℕ), ∀ t, ‖Θ t‖ ≤ A * (1 + |t|) ^ k) :
    Integrable (fun t : ℝ => conj (∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) * Θ t) := by
  obtain ⟨A, k, hA⟩ := hΘg
  obtain ⟨C, hC0, hC⟩ := exists_norm_FI_le h hh hc (k + 2)
  have hcont := continuous_FI h hh hc
  have hcont' : Continuous (fun t : ℝ => conj (∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)))) :=
    Complex.continuous_conj.comp hcont
  refine Integrable.mono' (aux_integrable_one_add_abs_rpow_neg_two (C * A))
    (hcont'.mul hΘ).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_conj]
  have hx : 0 < 1 + |t| := by positivity
  have hb : 0 ≤ C * (1 + |t|) ^ (-((k + 2 : ℕ) : ℝ)) := mul_nonneg hC0 (Real.rpow_nonneg hx.le _)
  calc ‖∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ * ‖Θ t‖
      ≤ (C * (1 + |t|) ^ (-((k + 2 : ℕ) : ℝ))) * (A * (1 + |t|) ^ k) :=
        mul_le_mul (hC t) (hA t) (norm_nonneg _) hb
    _ = C * A * ((1 + |t|) ^ (-((k + 2 : ℕ) : ℝ)) * (1 + |t|) ^ ((k : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
        ring
    _ = C * A * (1 + |t|) ^ (-(2:ℝ)) := by
        rw [← Real.rpow_add hx]
        congr 1
        congr 1
        push_cast
        ring

theorem integrable_norm_FI_sq (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    Integrable (fun t : ℝ => ‖∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_FI_le h hh hc 2
  have hcont := continuous_FI h hh hc
  refine Integrable.mono' (aux_integrable_one_add_abs_rpow_neg_two (C * C))
    (hcont.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_pow, norm_norm]
  have hx1 : 1 ≤ 1 + |t| := by
    have := abs_nonneg t
    linarith
  have h1 : ‖∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ ≤ C * (1 + |t|) ^ (-(2:ℝ)) := by
    have := hC t
    simpa only [Nat.cast_ofNat] using this
  have h2 : ‖∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ ≤ C :=
    h1.trans (mul_le_of_le_one_right hC0 (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)))
  calc ‖∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ ^ 2
      = ‖∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖
          * ‖∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ := sq _
    _ ≤ (C * (1 + |t|) ^ (-(2:ℝ))) * C := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = C * C * (1 + |t|) ^ (-(2:ℝ)) := by ring

end FIKit

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ C : ℝ, 0 < C ∧
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨm : Measurable Ψ)
      (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
      (_hΨb : ∃ M : ℝ, ∀ y, ‖Ψ y‖ ≤ M),
    (∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ =>
        (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) 2) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e),
        ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2) ∧
    ∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e),
        ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2
      ≤ C * ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ‖(fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  intro αm hαm
  obtain ⟨CR, hCR, hR⟩ := AutomorphicForm.exists_matched_paleyWiener_sum_integral_sum_conj_inner_mul_eq_sum_integral_sum_conj_integral_mul_cexp_mul_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm
  obtain ⟨κ₁, hκ₁, hWP⟩ := AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm
  refine ⟨CR / κ₁ ^ 2, by positivity, ?_⟩
  intro ι b cls hb hbn hbo hbs hbc ιE _ μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE Ψ hΨm hΨc hΨb
  obtain ⟨ρ, hρm, hρmom, hρ1, hρconv⟩ := MeasureTheory.exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp
  have hΨauto := AutomorphicForm.isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain K α β hα hαβ νZK ξK hξc hξt hξu Ψ hΨm hΨc hΨb
  obtain ⟨TΨ, hTΨ⟩ := AutomorphicForm.exists_forall_mem_canonicalTruncationDomain_finsum_integral_indicator_eq_zero_of_lt_adelicHeight K α β hα hαβ νZK ξK Ψ hΨc
  have hcont := fun (e : ιE) (j : Fin (nE e)) =>
    AutomorphicForm.continuous_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE Ψ hΨm hΨc hΨb e j
  have memLp_of_auto : ∀ f : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK f → MemLp f 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
    intro f hf
    have hf' := hf
    unfold IsAutomorphicFnAt at hf'
    rw [AutomorphicForm.lsXiMemberAt_iff] at hf'
    exact hf'.2
  have mθΨ := memLp_of_auto _ hΨauto

  set I₀ : ℝ := ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ‖(fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hI₀
  have hI₀nn : 0 ≤ I₀ := integral_nonneg (fun g => by positivity)
  set M₀ : ℝ := κ₁⁻¹ * Real.sqrt CR * Real.sqrt I₀ with hM₀
  have hM₀nn : 0 ≤ M₀ := by positivity

  have claim : ∀ F : Finset ιE,
      (∀ p : (Σ e : ↥F, Fin (nE (e : ιE))), MemLp (fun t : ℝ => (fun (e : ιE) (j : Fin (nE e)) (t : ℝ) => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) (p.1 : ιE) p.2 t) 2) ∧
      ∑ p : (Σ e : ↥F, Fin (nE (e : ιE))), ∫ t : ℝ, ‖(fun (e : ιE) (j : Fin (nE e)) (t : ℝ) => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) (p.1 : ιE) p.2 t‖ ^ 2 ≤ M₀ ^ 2 := by
    intro F
    refine MeasureTheory.memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le
      (fun (p : (Σ e : ↥F, Fin (nE (e : ιE)))) (t : ℝ) => (fun (e : ιE) (j : Fin (nE e)) (t : ℝ) => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) (p.1 : ιE) p.2 t)
      (fun p => (hcont (p.1 : ιE) p.2).1) (fun p => (hcont (p.1 : ιE) p.2).2) ρ hρm hρmom hρ1 M₀ ?_
    intro u hum huR huB δ hδ hδ1
    have hsel : ∀ p : (Σ e : ↥F, Fin (nE (e : ιE))), ∃ hh : ℝ → ℂ, ContDiff ℝ ∞ hh ∧ HasCompactSupport hh ∧
        ∀ t : ℝ, (∫ x : ℝ, u p x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)) = (∫ x : ℝ, hh x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) := by
      intro p
      obtain ⟨R, hR'⟩ := huR
      obtain ⟨B, hB⟩ := huB
      exact hρconv (u p) (hum p) ⟨R, hR' p⟩ ⟨B, hB p⟩ δ hδ
    choose hh hh_smooth hh_cpt hh_eq using hsel
    classical
    let hfull : (e : ιE) → Fin (nE e) → ℝ → ℂ := fun e j =>
      if he : e ∈ F then hh ⟨⟨e, he⟩, j⟩ else 0
    have hfull_reg : ∀ (e : ιE) (j : Fin (nE e)), ContDiff ℝ ∞ (hfull e j) ∧ HasCompactSupport (hfull e j) := by
      intro e j
      by_cases he : e ∈ F
      · simp only [hfull, dif_pos he]; exact ⟨hh_smooth _, hh_cpt _⟩
      · simp only [hfull, dif_neg he]; exact ⟨contDiff_const, HasCompactSupport.zero⟩
    have hfull_off : ∀ (e : ιE), e ∉ F → ∀ (j : Fin (nE e)), hfull e j = 0 := by
      intro e he j; simp only [hfull, dif_neg he]
    have hfull_on : ∀ (e : ↥F) (j : Fin (nE (e : ιE))), hfull (e : ιE) j = hh ⟨e, j⟩ := by
      intro e j; simp only [hfull, dif_pos e.2]

    obtain ⟨ιP, instP, μP, νP, hμP, hνP, hμicP, hνicP, hμcP, hμνP, rP, hrP, hdistP, ψf, hψf, hψjc, hψhol, hψK, hψsm, hψKu, hνcP, hψdec, ψ, hψ, hψrep, em, τ, hem, hψlev, hψty, pψ, hpψ, hpψc, hpψo, hR1, hR2⟩ := hR ι b cls hb hbn hbo hbs hbc ιE μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE F hfull hfull_reg hfull_off

    obtain ⟨-, hA2⟩ := AutomorphicForm.setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP μP νP hμP hνP hμicP hνicP hμcP hμνP rP hrP hdistP ψf hψf hψjc hψhol hψK hψsm hψKu hνcP hψdec ψ hψ hψrep em τ hem hψlev hψty (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) hΨauto ⟨TΨ, hTΨ⟩
    have hWPae := hWP ι b cls hb hbn hbo hbs hbc ιE μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP μP νP hμP hνP hμicP hνicP hμcP hμνP rP hrP hdistP ψf hψf hψjc hψhol hψK hψsm hψKu hνcP hψdec ψ hψ hψrep em τ hem hψlev hψty pψ hpψ hpψc hpψo
    have hR1Θ := hR1 (fun (e : ιE) (j : Fin (nE e)) (t : ℝ) => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))

    have mθψ : MemLp (AutomorphicForm.pseudoEisenstein K ψ) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
      obtain ⟨-, -, -, hΦs, hΦfd⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
      exact memLp_of_auto _ (AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab K α β hα hαβ
        (AutomorphicForm.canonicalTruncationDomain K α β) hΦs hΦfd ξK ψ hψ)
    have mW : MemLp (fun g => AutomorphicForm.pseudoEisenstein K ψ g - pψ g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := mθψ.sub (memLp_of_auto _ hpψ)
    have hIW : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
        = (κ₁ : ℂ) * (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
        conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by
      rw [← hA2, ← L2Kit.integral_mul_conj_real_smul]
      apply integral_congr_ae
      filter_upwards [hWPae] with g hg
      rw [hg]

    have hint : ∀ (e : ιE) (j : Fin (nE e)), Integrable (fun t : ℝ => conj (∫ x : ℝ, (hfull e j) x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) * (fun (e : ιE) (j : Fin (nE e)) (t : ℝ) => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) e j t) :=
      fun e j => FIKit.integrable_conj_FI_mul (hfull e j) (hfull_reg e j).1 (hfull_reg e j).2 _ (hcont e j).1 (hcont e j).2
    have hLHS : (∑ p : (Σ e : ↥F, Fin (nE (e : ιE))), ∫ t : ℝ, conj (∫ x : ℝ, u p x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)) * (fun (e : ιE) (j : Fin (nE e)) (t : ℝ) => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) (p.1 : ιE) p.2 t)
        = (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
        conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by
      rw [hR1Θ]
      conv_rhs => rw [← Finset.sum_coe_sort]
      simp_rw [hh_eq]
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [integral_finset_sum _ (fun j _ => hint (e : ιE) j)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hfull_on]

    have hRHS : (∑ p : (Σ e : ↥F, Fin (nE (e : ιE))), ∫ t : ℝ, ‖(∫ x : ℝ, u p x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ))‖ ^ 2)
        = ∑ e ∈ F, ∑ j : Fin (nE e), ∫ t : ℝ, ‖(∫ x : ℝ, (hfull e j) x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)))‖ ^ 2 := by
      conv_rhs => rw [← Finset.sum_coe_sort]
      rw [Fintype.sum_sigma]
      simp_rw [hh_eq]
      refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hfull_on]

    rw [hLHS, hRHS]
    have hX : (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
        conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) = ((κ₁⁻¹ : ℝ) : ℂ) * (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
      rw [hIW, ← mul_assoc]; push_cast; rw [inv_mul_cancel₀ (by exact_mod_cast hκ₁.ne')]; ring
    rw [hX, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκ₁)]
    have hCS := L2Kit.norm_integral_mul_conj_le mθΨ mW
    have hWn : Real.sqrt (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        ‖AutomorphicForm.pseudoEisenstein K ψ g - pψ g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
        ≤ Real.sqrt CR * Real.sqrt (∑ e ∈ F, ∑ j : Fin (nE e), ∫ t : ℝ, ‖(∫ x : ℝ, (hfull e j) x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)))‖ ^ 2) := by
      rw [← Real.sqrt_mul hCR.le]
      exact Real.sqrt_le_sqrt hR2
    calc κ₁⁻¹ * ‖∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
        ≤ κ₁⁻¹ * (Real.sqrt I₀ * Real.sqrt (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            ‖AutomorphicForm.pseudoEisenstein K ψ g - pψ g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by
          rw [hI₀]; gcongr
      _ ≤ κ₁⁻¹ * (Real.sqrt I₀ * (Real.sqrt CR * Real.sqrt (∑ e ∈ F, ∑ j : Fin (nE e), ∫ t : ℝ, ‖(∫ x : ℝ, (hfull e j) x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)))‖ ^ 2))) := by
          gcongr
      _ = M₀ * Real.sqrt (∑ e ∈ F, ∑ j : Fin (nE e), ∫ t : ℝ, ‖(∫ x : ℝ, (hfull e j) x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)))‖ ^ 2) := by
          rw [hM₀]; ring

  have hint2 : ∀ (e : ιE) (j : Fin (nE e)), Integrable (fun t : ℝ => ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2) := by
    intro e j
    have hm := (claim {e}).1 ⟨⟨e, Finset.mem_singleton_self e⟩, j⟩
    exact (memLp_two_iff_integrable_sq_norm hm.1).1 hm
  have hnonneg : ∀ e : ιE, 0 ≤ ∫ t : ℝ, ∑ j : Fin (nE e), ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2 :=
    fun e => integral_nonneg (fun t => Finset.sum_nonneg (fun j _ => by positivity))
  have hpartial : ∀ F : Finset ιE,
      ∑ e ∈ F, ∫ t : ℝ, ∑ j : Fin (nE e), ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2 ≤ M₀ ^ 2 := by
    intro F
    have hc := (claim F).2
    calc ∑ e ∈ F, ∫ t : ℝ, ∑ j : Fin (nE e), ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2
        = ∑ e ∈ F, ∑ j : Fin (nE e), ∫ t : ℝ, ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          exact integral_finset_sum _ (fun j _ => hint2 e j)
      _ = ∑ e : ↥F, ∑ j : Fin (nE (e : ιE)), ∫ t : ℝ, ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE (e : ιE) j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2 := by
          rw [← Finset.sum_coe_sort]
      _ = ∑ p : (Σ e : ↥F, Fin (nE (e : ιE))), ∫ t : ℝ, ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE (p.1 : ιE) p.2 ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2 := by
          rw [Fintype.sum_sigma]
      _ ≤ M₀ ^ 2 := hc
  have hM₀sq : M₀ ^ 2 = CR / κ₁ ^ 2 * I₀ := by
    rw [hM₀, mul_pow, mul_pow, Real.sq_sqrt hCR.le, Real.sq_sqrt hI₀nn, inv_pow]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro e j
    exact (claim {e}).1 ⟨⟨e, Finset.mem_singleton_self e⟩, j⟩
  · exact summable_of_sum_le hnonneg hpartial
  · rw [hI₀] at hM₀sq
    rw [← hM₀sq]
    exact Real.tsum_le_of_sum_le hnonneg hpartial

end S_AutomorphicForm_exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq (solution)
