-- Prove2me | solution 1 for AutomorphicForm.memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1dbb9727-49ed-5e88-be30-c0716b2e3dfd

import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half
import Theorems.Thm_AutomorphicForm_bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchType
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U"
p2m_attr_erase "simp" "AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace R1L2Trunc

open MeasureTheory Set NumberField IsDedekindDomain Filter
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicHeight

open scoped NNReal ENNReal Topology Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
set_option quotPrecheck false in

local notation "αF" => (MonoidHom.toHomUnits
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))) :
    (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)

section Height

variable {F}

theorem haarMod_apply (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((αF x : ℝˣ) : ℝ) = ((distribHaarChar 𝔸 x : ℝ≥0) : ℝ) := rfl

variable (F) in

theorem exists_borel_mul_maximalCompact_eq (g : AdelicGL2 (𝓞 F) F) :
    ∃ (b : ↥(adelicBorel (𝓞 F) F)) (k : ↥(adelicMaximalCompact F)),
      g = (b : AdelicGL2 (𝓞 F) F) * (k : AdelicGL2 (𝓞 F) F) := by
  obtain ⟨b, k, hb, hk₁, hk₂, hg⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  exact ⟨⟨b, hb⟩, ⟨k, mem_adelicMaximalCompact_iff.2 ⟨hk₁, hk₂⟩⟩, hg⟩

theorem adelicHeight_borel_mul (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) {b : AdelicGL2 (𝓞 F) F}
    (hb : b ∈ adelicBorel (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (b * g)
      = ((αF (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ)
        * (((αF (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ))⁻¹
        * adelicHeight F g := by
  have h := (AutomorphicForm.isInducedSection_adelicHeight_cpow F).2.2 hα (1 / 2) b hb g
  have e1 : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
  simp only [e1, Complex.cpow_one, etaFst_apply, etaSnd_apply, MonoidHom.one_apply,
    one_mul, cpowChar_apply_val, Complex.cpow_neg_one] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

theorem adelicHeight_of_mem_maximalCompact {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ adelicMaximalCompact F) :
    adelicHeight F k = 1 := by
  rw [adelicHeight_eq_archHeight_of_mem (glFin_mem_finiteIntegralGL2 hk)]
  have h := archHeight_mul_rowIsometry F 1 (k := glArch (𝓞 F) F k) (isRowIsometry_archComponent hk)
  rwa [one_mul, archHeight_one] at h

theorem adelicHeight_mul_of_mem_maximalCompact (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    (g : AdelicGL2 (𝓞 F) F) {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ adelicMaximalCompact F) :
    adelicHeight F (g * k) = adelicHeight F g := by
  obtain ⟨b, k', hg⟩ := exists_borel_mul_maximalCompact_eq F g
  rw [hg, mul_assoc, adelicHeight_borel_mul hα b.2, adelicHeight_borel_mul hα b.2 (k' : AdelicGL2 (𝓞 F) F),
    adelicHeight_of_mem_maximalCompact ((adelicMaximalCompact F).mul_mem k'.2 hk),
    adelicHeight_of_mem_maximalCompact k'.2]

theorem ratio_pos (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (a d : (AdeleRing (𝓞 F) F)ˣ) :
    0 < ((αF a : ℝˣ) : ℝ) * (((αF d : ℝˣ) : ℝ))⁻¹ :=
  mul_pos (hα a) (inv_pos.2 (hα d))

end Height

section Gauge

variable {F}

theorem norm_etaSnd_apply_of_unitary {ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hν : IsUnitaryChar (𝓞 F) F ν)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((etaSnd ν α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ (-(s.re + 1 / 2)) := by
  rw [etaSnd_apply, Units.val_mul, norm_mul, hν x, one_mul, norm_cpowChar_apply]
  congr 1
  rw [Complex.neg_re, re_add_half]

theorem norm_apply_borel_mul (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (s : ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) φ)
    {b : AdelicGL2 (𝓞 F) F} (hb : b ∈ adelicBorel (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    ‖φ (b * g)‖ = (((αF (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ)
        * (((αF (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ))⁻¹) ^ (s.re + 1 / 2)
      * ‖φ g‖ := by
  rw [hφ b hb g, norm_mul, norm_mul, norm_etaFst_apply_of_unitary hμ, norm_etaSnd_apply_of_unitary hν,
    Real.mul_rpow (le_of_lt (hα _)) (inv_nonneg.2 (le_of_lt (hα _))), Real.inv_rpow (le_of_lt (hα _)),
    Real.rpow_neg (le_of_lt (hα _))]

theorem norm_apply_le_gauge (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (s : ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) φ)
    {C : ℝ} (hC : ∀ k ∈ adelicMaximalCompact F, ‖φ k‖ ≤ C) (g : AdelicGL2 (𝓞 F) F) :
    ‖φ g‖ ≤ C * adelicHeight F g ^ (s.re + 1 / 2) := by
  obtain ⟨b, k, hg⟩ := exists_borel_mul_maximalCompact_eq F g
  rw [hg, norm_apply_borel_mul hα hμ hν s hφ b.2, adelicHeight_borel_mul hα b.2,
    adelicHeight_of_mem_maximalCompact k.2, mul_one]
  have hr := Real.rpow_nonneg (ratio_pos hα (borelDiagFst (⟨(b : AdelicGL2 (𝓞 F) F), b.2⟩ : ↥(adelicBorel (𝓞 F) F)))
    (borelDiagSnd (⟨(b : AdelicGL2 (𝓞 F) F), b.2⟩ : ↥(adelicBorel (𝓞 F) F)))).le (s.re + 1 / 2)
  rw [mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC _ k.2) hr

theorem exists_bound_on_maximalCompact_mul {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    {T : Set (AdelicGL2 (𝓞 F) F)} (hT : IsCompact T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ adelicMaximalCompact F, ∀ y ∈ T, ‖φ (k * y)‖ ≤ C := by
  have hc : IsCompact ((fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => p.1 * p.2) ''
      ((adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) ×ˢ T)) :=
    ((isCompact_adelicMaximalCompact (K := F)).prod hT).image continuous_mul
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hφc.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun k hk y hy =>
    (hC _ ⟨(k, y), ⟨hk, hy⟩, rfl⟩).trans (le_max_left _ _)⟩

theorem continuous_rightTranslate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ) (y : AdelicGL2 (𝓞 F) F) :
    Continuous fun h : AdelicGL2 (𝓞 F) F => φ (h * y) :=
  hφc.comp (continuous_id.mul continuous_const)

end Gauge

section Spherical

variable {F}

def sR (s : ℂ) : ℂ := ((s.re : ℝ) : ℂ)

theorem sR_re (s : ℂ) : (sR s).re = s.re := Complex.ofReal_re _

theorem one_half_lt_sR_re {s : ℂ} (hs : 1 / 2 < s.re) : 1 / 2 < (sR s).re := by rwa [sR_re]

variable (F) in

def sph (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ := ((adelicHeight F g : ℝ) : ℂ) ^ (sR s + 1 / 2)

theorem sph_eq_ofReal (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    sph F s g = ((adelicHeight F g ^ (s.re + 1 / 2) : ℝ) : ℂ) := by
  unfold sph sR
  rw [Complex.ofReal_cpow (adelicHeight_pos g).le]
  push_cast
  rfl

theorem norm_sph (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ‖sph F s g‖ = adelicHeight F g ^ (s.re + 1 / 2) := by
  rw [sph_eq_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (adelicHeight_pos g).le _)]

theorem sph_eq_norm (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : sph F s g = ((‖sph F s g‖ : ℝ) : ℂ) := by
  rw [norm_sph, sph_eq_ofReal]

theorem isUnitaryChar_one : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :=
  (AutomorphicForm.isInducedSection_adelicHeight_cpow F).2.1

theorem isInducedSection_sph (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (s : ℂ) :
    IsInducedSection (𝓞 F) F (etaFst 1 αF hα (sR s)) (etaSnd 1 αF hα (sR s)) (sph F s) :=
  (AutomorphicForm.isInducedSection_adelicHeight_cpow F).2.2 hα (sR s)

theorem continuous_sph (s : ℂ) : Continuous (sph F s) := by
  unfold sph
  refine Continuous.cpow (Complex.continuous_ofReal.comp (NumberField.AdelicHeight.continuous_adelicHeight F))
    continuous_const fun g => ?_
  exact Complex.ofReal_mem_slitPlane.2 (adelicHeight_pos g)

theorem sph_mul_of_mem_maximalCompact (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (s : ℂ) (g : AdelicGL2 (𝓞 F) F)
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ adelicMaximalCompact F) : sph F s (g * k) = sph F s g := by
  unfold sph
  rw [adelicHeight_mul_of_mem_maximalCompact hα g hk]

theorem norm_sph_le_one_of_mem (s : ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ adelicMaximalCompact F) :
    ‖sph F s k‖ ≤ 1 := by
  rw [norm_sph, adelicHeight_of_mem_maximalCompact hk, Real.one_rpow]

theorem adelicArchGLInclAt_mem (w : InfinitePlace F) (k : ↥(rowIsometrySubgroup w.Completion)) :
    adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) ∈ adelicMaximalCompact F := by
  refine ⟨?_, fun v => ?_⟩
  · show glFin (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w (k : GL (Fin 2) w.Completion))) ∈ _
    rw [glFin_adelicArchGLIncl]
    exact Subgroup.one_mem _
  · show IsRowIsometry (archComponent F v (glArch (𝓞 F) F
      (adelicArchGLIncl F (archGLIncl F w (k : GL (Fin 2) w.Completion)))))
    rw [glArch_adelicArchGLIncl]
    by_cases hvw : v = w
    · subst hvw
      rw [archComponent_archGLIncl_self]
      exact k.2
    · rw [archComponent_archGLIncl_of_ne F hvw]
      exact isRowIsometry_one

theorem isArchKFinite_sph (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (s : ℂ) : IsArchKFinite F (sph F s) := by
  refine isArchKFinite_of_hasArchType F (fun _ => 1) (sph F s) fun w k g => ?_
  rw [sph_mul_of_mem_maximalCompact hα s g (adelicArchGLInclAt_mem w k)]
  simp

theorem mem_maximalCompact_of_glArch_eq_one {k : AdelicGL2 (𝓞 F) F} (h1 : glArch (𝓞 F) F k = 1)
    (h2 : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F) : k ∈ adelicMaximalCompact F := by
  refine ⟨h2, fun w => ?_⟩
  rw [h1, map_one]
  exact isRowIsometry_one

theorem isKfSmooth_sph (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (s : ℂ) : IsKfSmooth F (sph F s) := by
  let G' : Subgroup (AdelicGL2 (𝓞 F) F) := finiteAdelicGL2Subgroup F
  let Hs : Subgroup ↥G' := (levelZero (𝓞 F) F (⊤ : Ideal (𝓞 F))).comap G'.subtype
  have hHs : IsOpen (Hs : Set ↥G') :=
    (isOpen_levelZero (𝓞 F) F (N := (⊤ : Ideal (𝓞 F))) (by simp)).preimage continuous_subtype_val
  refine FLT.SmoothVectors.IsSmoothVector.of_isOpen_subgroup Hs hHs ?_
  rw [FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer]
  convert isOpen_univ using 2
  rw [Set.eq_univ_iff_forall]
  intro h
  refine MulAction.mem_stabilizer_iff.mpr (FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_)
  change sph F s (x * ((h : ↥G') : AdelicGL2 (𝓞 F) F)) = sph F s x
  refine sph_mul_of_mem_maximalCompact hα s x (mem_maximalCompact_of_glArch_eq_one ?_ ?_)
  · exact (mem_finiteAdelicGL2Subgroup_iff F _).1 (h : ↥G').2
  · exact h.2

variable (F) in

def bigCell (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (ι ξ) * g)

theorem pseudoEisenstein_eq (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    pseudoEisenstein F φ = fun g => φ g + bigCell F φ g := rfl

variable (F) in

def sphSum (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  ∑' ξ : F, ‖sph F s (adelicWeyl (𝓞 F) F * unipotentGL2 (ι ξ) * g)‖

theorem summable_sph (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) {s : ℂ} (hs : 1 / 2 < s.re) (g : AdelicGL2 (𝓞 F) F) :
    Summable fun ξ : F => ‖sph F s (adelicWeyl (𝓞 F) F * unipotentGL2 (ι ξ) * g)‖ :=
  AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hα 1 1 isUnitaryChar_one
    isUnitaryChar_one (sR s) (one_half_lt_sR_re hs) (sph F s) (isInducedSection_sph hα s) (continuous_sph s) g

theorem sphSum_nonneg (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : 0 ≤ sphSum F s g :=
  tsum_nonneg fun _ => norm_nonneg _

theorem sph_bigCell_eq_ofReal (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    bigCell F (sph F s) g = ((sphSum F s g : ℝ) : ℂ) := by
  unfold bigCell sphSum
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun ξ => sph_eq_norm s _

theorem norm_sph_bigCell (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ‖bigCell F (sph F s) g‖ = sphSum F s g := by
  rw [sph_bigCell_eq_ofReal, Complex.norm_real, Real.norm_of_nonneg (sphSum_nonneg s g)]

theorem norm_bigCell_le (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    {s : ℂ} (hs : 1 / 2 < s.re) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) φ) (hφc : Continuous φ)
    {C : ℝ} (hC : ∀ k ∈ adelicMaximalCompact F, ‖φ k‖ ≤ C) (g : AdelicGL2 (𝓞 F) F) :
    ‖bigCell F φ g‖ ≤ C * sphSum F s g := by
  have hsum := AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hα μ ν hμ hν s hs φ hφ
    hφc g
  unfold bigCell sphSum
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun ξ => ?_) hsum ((summable_sph hα hs g).mul_left C)
  rw [norm_sph]
  exact norm_apply_le_gauge hα hμ hν s hφ hC _

end Spherical

section Intertwining

variable {F}

scoped instance regular_adelicAddHaar :
    @Measure.Regular 𝔸 (adeleBorel (𝓞 F) F) _ (adelicAddHaar (𝓞 F) F) := by
  show Measure.Regular (Measure.addHaar)
  infer_instance

scoped instance isAddHaarMeasure_adelicAddHaar' : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure :=
  isAddHaarMeasure_adelicAddHaar (𝓞 F) F

theorem integral_comp_units_mul (u : (AdeleRing (𝓞 F) F)ˣ) (f : AdeleRing (𝓞 F) F → ℂ) :
    ∫ x, f ((u : 𝔸) * x) ∂(adelicAddHaar (𝓞 F) F)
      = ((distribHaarChar 𝔸 u : ℝ≥0) : ℝ)⁻¹ • ∫ x, f x ∂(adelicAddHaar (𝓞 F) F) := by
  set μ := adelicAddHaar (𝓞 F) F with hμ
  have hmap : Measure.map (fun x : 𝔸 => (u : 𝔸) * x) μ = (distribHaarChar 𝔸 u)⁻¹ • μ := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply]
    have hpre : (fun x : 𝔸 => (u : 𝔸) * x) ⁻¹' s = u⁻¹ • s := by
      ext x
      simp only [Set.mem_preimage]
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]
    rw [hpre, ← distribHaarChar_mul μ u⁻¹ s, map_inv]
    rfl
  set e : 𝔸 ≃ᵐ 𝔸 := (Homeomorph.smul u).toMeasurableEquiv with hedef
  have he : (e : 𝔸 → 𝔸) = fun x => (u : 𝔸) * x := by
    funext x; rfl
  calc ∫ x, f ((u : 𝔸) * x) ∂μ
      = ∫ x, f (e x) ∂μ := by rw [he]
    _ = ∫ y, f y ∂(Measure.map e μ) := (integral_map_equiv e f).symm
    _ = ∫ y, f y ∂((distribHaarChar 𝔸 u)⁻¹ • μ) := by rw [he, hmap]
    _ = ((distribHaarChar 𝔸 u : ℝ≥0) : ℝ)⁻¹ • ∫ x, f x ∂μ := by
        rw [integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_inv]

section Diag

variable {A : Type*} [CommRing A]

def diagGL (p q : Aˣ) : GL (Fin 2) A where
  val := !![(p : A), 0; 0, (q : A)]
  inv := !![((p⁻¹ : Aˣ) : A), 0; 0, ((q⁻¹ : Aˣ) : A)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem diagGL_val (p q : Aˣ) :
    ((diagGL p q : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(p : A), 0; 0, (q : A)] := rfl

theorem diagGL_mem_borelSubgroup (p q : Aˣ) : diagGL p q ∈ borelSubgroup A := by
  show ((diagGL p q : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
  simp

theorem borelDiagFst_diagGL (p q : Aˣ) :
    borelDiagFst (⟨diagGL p q, diagGL_mem_borelSubgroup p q⟩ : ↥(borelSubgroup A)) = p :=
  Units.ext rfl

theorem borelDiagSnd_diagGL (p q : Aˣ) :
    borelDiagSnd (⟨diagGL p q, diagGL_mem_borelSubgroup p q⟩ : ↥(borelSubgroup A)) = q :=
  Units.ext rfl

end Diag

theorem adelicWeyl_inv_val :
    (((adelicWeyl (𝓞 F) F)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, 0] := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]
  ext i j
  rw [globalPoints_apply, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp

theorem weylInv_mul_unipotent_mul_borel (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F)
    (x : 𝔸) :
    (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * b
      = diagGL (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))
          (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))
        * ((adelicWeyl (𝓞 F) F)⁻¹
          * unipotentGL2
              (((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : 𝔸ˣ)
                  * (b : Matrix (Fin 2) (Fin 2) 𝔸) 0 1
                + ((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : 𝔸ˣ)
                  * (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 * x)) := by
  have hb0 : (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0 := hb
  have ha : (b : Matrix (Fin 2) (Fin 2) 𝔸) 0 0
      * (((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : 𝔸ˣ) : 𝔸) = 1 :=
    (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))).mul_inv
  apply Units.ext
  simp only [Units.val_mul, adelicWeyl_inv_val, unipotentGL2_coe, diagGL_val,
    borelDiagFst_apply_val, borelDiagSnd_apply_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb0]
  linear_combination (-((b : Matrix (Fin 2) (Fin 2) 𝔸) 0 1
    + (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 * x)) * ha

theorem weylIntertwiningIntegral_borel_mul (χ₁ χ₂ : 𝔸ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ)
    (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ (b * g)
      = ((χ₁ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((χ₂ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * (((distribHaarChar 𝔸
              ((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹
                * borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝ≥0) : ℝ) : ℂ)⁻¹
        * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by
  set a : 𝔸ˣ := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with ha
  set d : 𝔸ˣ := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with hd
  set c : 𝔸 := (b : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 with hc
  have hd' : (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 = (d : 𝔸) := rfl
  have hpt : ∀ x : 𝔸,
      φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (b * g))
        = ((χ₁ d : ℂˣ) : ℂ) * ((χ₂ a : ℂˣ) : ℂ)
          * φ ((adelicWeyl (𝓞 F) F)⁻¹
              * unipotentGL2 ((a⁻¹ : 𝔸ˣ) * c + ((a⁻¹ * d : 𝔸ˣ) : 𝔸) * x) * g) := by
    intro x
    rw [← mul_assoc, weylInv_mul_unipotent_mul_borel b hb x, mul_assoc,
      hφ _ (diagGL_mem_borelSubgroup d a), borelDiagFst_diagGL, borelDiagSnd_diagGL, hd',
      Units.val_mul, mul_assoc ((a⁻¹ : 𝔸ˣ) : 𝔸) (d : 𝔸) x]
  unfold weylIntertwiningIntegral
  simp_rw [hpt]
  rw [integral_const_mul]
  have hdil := integral_comp_units_mul (F := F) (a⁻¹ * d)
    (fun y => φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 ((a⁻¹ : 𝔸ˣ) * c + y) * g))
  have htr : ∫ y, φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 ((a⁻¹ : 𝔸ˣ) * c + y) * g)
      ∂(adelicAddHaar (𝓞 F) F)
      = ∫ y, φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 y * g) ∂(adelicAddHaar (𝓞 F) F) :=
    integral_add_left_eq_self (μ := adelicAddHaar (𝓞 F) F)
      (fun y => φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 y * g)) ((a⁻¹ : 𝔸ˣ) * c)
  rw [hdil, htr, Complex.real_smul, Complex.ofReal_inv]
  ring

variable (F) in

def sphInt (s : ℂ) : ℝ :=
  ∫ t, ‖sph F s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 t * 1)‖ ∂(adelicAddHaar (𝓞 F) F)

theorem sphInt_nonneg (s : ℂ) : 0 ≤ sphInt F s := integral_nonneg fun _ => norm_nonneg _

theorem integrable_sph_weyl (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (fun t : 𝔸 => sph F s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 t * 1)) (adelicAddHaar (𝓞 F) F) :=
  AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα 1 1 isUnitaryChar_one isUnitaryChar_one
    (sR s) (one_half_lt_sR_re hs) (sph F s) (isInducedSection_sph hα s) (continuous_sph s) 1

theorem moduli_bookkeeping {a d : ℝ} (ha : 0 < a) (hd : 0 < d) (σ : ℝ) :
    d ^ (σ + 1 / 2) * a ^ (-(σ + 1 / 2)) * (a⁻¹ * d)⁻¹ = (a * d⁻¹) ^ (1 / 2 - σ) := by
  have had : 0 < a * d⁻¹ := mul_pos ha (inv_pos.2 hd)
  have h1 : (1 / 2 - σ : ℝ) = 1 + (-(σ + 1 / 2)) := by ring
  rw [h1, Real.rpow_add had, Real.rpow_one, Real.rpow_neg had.le, Real.mul_rpow ha.le (inv_nonneg.2 hd.le),
    Real.inv_rpow hd.le, Real.rpow_neg ha.le, mul_inv, inv_inv]
  field_simp

theorem norm_weylIntertwiningIntegral_le (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    {s : ℂ} (hs : 1 / 2 < s.re) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) φ) (hφc : Continuous φ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ k ∈ adelicMaximalCompact F, ‖φ k‖ ≤ C) (g : AdelicGL2 (𝓞 F) F) :
    ‖weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g‖
      ≤ C * sphInt F s * adelicHeight F g ^ (1 / 2 - s.re) := by
  obtain ⟨b, k, hg⟩ := exists_borel_mul_maximalCompact_eq F g
  rw [hg, weylIntertwiningIntegral_borel_mul _ _ φ hφ (b : AdelicGL2 (𝓞 F) F) b.2, adelicHeight_borel_mul hα b.2,
    adelicHeight_of_mem_maximalCompact k.2, mul_one]
  set a : 𝔸ˣ := borelDiagFst (⟨(b : AdelicGL2 (𝓞 F) F), b.2⟩ : ↥(adelicBorel (𝓞 F) F)) with ha_def
  set d : 𝔸ˣ := borelDiagSnd (⟨(b : AdelicGL2 (𝓞 F) F), b.2⟩ : ↥(adelicBorel (𝓞 F) F)) with hd_def

  have hk : ‖weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ (k : AdelicGL2 (𝓞 F) F)‖
      ≤ C * sphInt F s := by
    unfold weylIntertwiningIntegral sphInt
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le ((integrable_sph_weyl hα hs).norm.const_mul C)
      (Filter.Eventually.of_forall fun t => ?_)
    calc ‖φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 t * (k : AdelicGL2 (𝓞 F) F))‖
        ≤ C * adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 t * (k : AdelicGL2 (𝓞 F) F))
            ^ (s.re + 1 / 2) := norm_apply_le_gauge hα hμ hν s hφ hC _
      _ = C * ‖sph F s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 t * 1)‖ := by
          rw [norm_sph, mul_one, adelicHeight_mul_of_mem_maximalCompact hα _ k.2]

  have hmod : ‖((etaFst μ αF hα s d : ℂˣ) : ℂ)‖ * ‖((etaSnd ν αF hα s a : ℂˣ) : ℂ)‖
      * ‖((((distribHaarChar 𝔸 (a⁻¹ * d) : ℝ≥0) : ℝ) : ℂ))⁻¹‖
      = (((αF a : ℝˣ) : ℝ) * (((αF d : ℝˣ) : ℝ))⁻¹) ^ (1 / 2 - s.re) := by
    rw [norm_etaFst_apply_of_unitary hμ, norm_etaSnd_apply_of_unitary hν, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg NNReal.zero_le_coe, map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv]
    exact moduli_bookkeeping (hα a) (hα d) s.re
  calc ‖((etaFst μ αF hα s d : ℂˣ) : ℂ) * ((etaSnd ν αF hα s a : ℂˣ) : ℂ)
        * (((distribHaarChar 𝔸 (a⁻¹ * d) : ℝ≥0) : ℝ) : ℂ)⁻¹
        * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ (k : AdelicGL2 (𝓞 F) F)‖
      = (((αF a : ℝˣ) : ℝ) * (((αF d : ℝˣ) : ℝ))⁻¹) ^ (1 / 2 - s.re)
        * ‖weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ (k : AdelicGL2 (𝓞 F) F)‖ := by
          rw [norm_mul, norm_mul, norm_mul, hmod]
    _ ≤ (((αF a : ℝˣ) : ℝ) * (((αF d : ℝˣ) : ℝ))⁻¹) ^ (1 / 2 - s.re) * (C * sphInt F s) :=
          mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg (ratio_pos hα a d).le _)
    _ = C * sphInt F s * (((αF a : ℝˣ) : ℝ) * (((αF d : ℝˣ) : ℝ))⁻¹) ^ (1 / 2 - s.re) := by ring

end Intertwining

section SiegelBound

variable {F}

theorem sR_sR (s : ℂ) : sR (sR s) = sR s := by
  unfold sR
  rw [Complex.ofReal_re]

theorem sph_sR (s : ℂ) : sph F (sR s) = sph F s := by
  funext g
  unfold sph
  rw [sR_sR]

theorem sphInt_sR (s : ℂ) : sphInt F (sR s) = sphInt F s := by
  unfold sphInt
  rw [sph_sR]

theorem isPrincipalTrivial_haarMod : IsPrincipalTrivial (R := 𝓞 F) (K := F) αF := by
  intro a
  apply Units.ext
  rw [MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, Units.val_one]
  have e : Units.map ((algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom) a
      = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) a := Units.ext rfl
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F a
  rw [e] at h
  rw [h, map_one]

theorem isIdeleClassChar_one : IsIdeleClassChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :=
  fun _ => rfl

theorem sph_globalPoints_mul (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (s : ℂ) {γ : GL (Fin 2) F}
    (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    sph F s (globalPoints (𝓞 F) F γ * g) = sph F s g := by
  have hmem := globalPoints_mem_adelicBorel (𝓞 F) F hγ
  rw [(isInducedSection_sph hα s) _ hmem g, borelDiagFst_globalPoints (𝓞 F) F hγ,
    borelDiagSnd_globalPoints (𝓞 F) F hγ,
    etaFst_isIdeleClassChar isIdeleClassChar_one isPrincipalTrivial_haarMod (sR s) _,
    etaSnd_isIdeleClassChar isIdeleClassChar_one isPrincipalTrivial_haarMod (sR s) _]
  simp

theorem mul_centralScalar_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    g * centralScalar (𝓞 F) F z = centralScalar (𝓞 F) F z * g := by
  apply Units.ext
  change (g : Matrix (Fin 2) (Fin 2) 𝔸) * (Matrix.scalar (Fin 2) (z : 𝔸))
    = (Matrix.scalar (Fin 2) (z : 𝔸)) * (g : Matrix (Fin 2) (Fin 2) 𝔸)
  exact ((Matrix.scalar_commute (z : 𝔸) (Commute.all _) (g : Matrix (Fin 2) (Fin 2) 𝔸)).eq).symm

theorem norm_sph_mul_centralScalar (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (s : ℂ) (g : AdelicGL2 (𝓞 F) F)
    (z : (AdeleRing (𝓞 F) F)ˣ) : ‖sph F s (g * centralScalar (𝓞 F) F z)‖ = ‖sph F s g‖ := by
  rw [mul_centralScalar_comm, isInducedSection_centralScalar_mul (isInducedSection_sph hα s), norm_mul,
    ← Units.val_mul, etaFst_mul_etaSnd]
  simp

theorem sphSum_mul_centralScalar (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) (s : ℂ) (g : AdelicGL2 (𝓞 F) F)
    (z : (AdeleRing (𝓞 F) F)ˣ) : sphSum F s (g * centralScalar (𝓞 F) F z) = sphSum F s g := by
  unfold sphSum
  refine tsum_congr fun ξ => ?_
  rw [← mul_assoc, norm_sph_mul_centralScalar hα]

theorem sph_bigCell_globalPoints_mul (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) {s : ℂ} (hs : 1 / 2 < s.re)
    {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    bigCell F (sph F s) (globalPoints (𝓞 F) F γ * g) = bigCell F (sph F s) g := by
  have hB : ∀ b ∈ borelSubgroup F, ∀ y : AdelicGL2 (𝓞 F) F, sph F s (globalPoints (𝓞 F) F b * y) = sph F s y :=
    fun b hb y => sph_globalPoints_mul hα s hb y
  have hsum : Summable fun ξ : F => sph F s (adelicWeyl (𝓞 F) F * unipotentGL2 (ι ξ) * g) :=
    (summable_sph hα hs g).of_norm
  have h := (AutomorphicForm.pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable F
    (sph F s) hB g hsum γ).2
  rw [pseudoEisenstein_eq] at h
  have h' : sph F s (globalPoints (𝓞 F) F γ * g) + bigCell F (sph F s) (globalPoints (𝓞 F) F γ * g)
      = sph F s g + bigCell F (sph F s) g := h
  rw [hB γ hγ g] at h'
  exact add_left_cancel h'

theorem exists_bound_sphSum_high (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) {s : ℂ} (hs : 1 / 2 < s.re) (c u : ℝ)
    (hc : 0 < c) :
    ∃ T₀ C : ℝ, ∀ g ∈ integralWindowedSiegelSet F c u,
      T₀ < archHeight F (glArch (𝓞 F) F g) → sphSum F s g ≤ C := by
  obtain ⟨T₀, hT₀⟩ := AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn F c u hα 1 1
    isUnitaryChar_one isUnitaryChar_one (sR s) (one_half_lt_sR_re hs) (sph F s) (isInducedSection_sph hα s)
    (isArchKFinite_sph hα s) (isKfSmooth_sph hα s) (continuous_sph s)
  obtain ⟨C₁, hC₁⟩ := hT₀ 0
  set κ : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ with hκ
  refine ⟨T₀, C₁ + ‖κ‖ * (1 * sphInt F s * c ^ (1 / 2 - s.re)), fun g hg hT => ?_⟩
  have h := hC₁ g ⟨hg, hT⟩
  have hCT := AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hα 1 1
    isUnitaryChar_one isUnitaryChar_one (sR s) (one_half_lt_sR_re hs) (sph F s) (isInducedSection_sph hα s)
    (continuous_sph s) g
  change ‖pseudoEisenstein F (sph F s) g
      - constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t)
          (pseudoEisenstein F (sph F s)) g‖ ≤ C₁ * (archHeight F (glArch (𝓞 F) F g))⁻¹ ^ 0 at h
  change constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t)
      (pseudoEisenstein F (sph F s)) g
      = sph F s g + κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (sph F s) g at hCT
  rw [pow_zero, mul_one, hCT, pseudoEisenstein_eq] at h
  have h' : ‖bigCell F (sph F s) g - κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (sph F s) g‖
      ≤ C₁ := by
    have e : sph F s g + bigCell F (sph F s) g
        - (sph F s g + κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (sph F s) g)
        = bigCell F (sph F s) g - κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (sph F s) g := by
      ring
    rw [← e]
    exact h

  have hHg : adelicHeight F g = archHeight F (glArch (𝓞 F) F g) := adelicHeight_eq_archHeight_of_mem hg.1
  have hcH : c ≤ adelicHeight F g := by rw [hHg]; exact hg.2.1
  have hM : ‖weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (sph F s) g‖
      ≤ 1 * sphInt F s * c ^ (1 / 2 - s.re) := by
    have h1 := norm_weylIntertwiningIntegral_le hα isUnitaryChar_one isUnitaryChar_one (one_half_lt_sR_re hs)
      (isInducedSection_sph hα s) (continuous_sph s) zero_le_one (fun k hk => norm_sph_le_one_of_mem s hk) g
    rw [sphInt_sR, sR_re] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg zero_le_one (sphInt_nonneg s)))
    exact Real.rpow_le_rpow_of_nonpos hc hcH (by linarith)
  calc sphSum F s g = ‖bigCell F (sph F s) g‖ := (norm_sph_bigCell s g).symm
    _ ≤ ‖bigCell F (sph F s) g - κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (sph F s) g‖
        + ‖κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (sph F s) g‖ :=
          norm_le_norm_sub_add _ _
    _ ≤ C₁ + ‖κ‖ * (1 * sphInt F s * c ^ (1 / 2 - s.re)) := by
          refine add_le_add h' ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hM (norm_nonneg _)

theorem exists_bound_sphSum_low (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) {s : ℂ} (hs : 1 / 2 < s.re) (c u T' : ℝ)
    (hc : 0 < c) :
    ∃ C : ℝ, ∀ g ∈ integralWindowedSiegelSet F c u,
      archHeight F (glArch (𝓞 F) F g) ≤ T' → sphSum F s g ≤ C := by
  obtain ⟨Kc, hKc, hcov⟩ := AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le F c u T' hc
  have hSc : Continuous (bigCell F (sph F s)) :=
    AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half F hα 1 1 isUnitaryChar_one isUnitaryChar_one
      (sR s) (one_half_lt_sR_re hs) (sph F s) (isInducedSection_sph hα s) (continuous_sph s)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hSc.continuousOn
  refine ⟨C, fun g hg hT => ?_⟩
  obtain ⟨γ, z, hγ, hmem⟩ := hcov g hg hT
  have hγB : γ ∈ borelSubgroup F := hγ
  calc sphSum F s g = sphSum F s (globalPoints (𝓞 F) F γ * g) := by
        rw [← norm_sph_bigCell, ← norm_sph_bigCell, sph_bigCell_globalPoints_mul hα hs hγB]
    _ = sphSum F s (globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z) :=
        (sphSum_mul_centralScalar hα s _ z).symm
    _ = ‖bigCell F (sph F s) (globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z)‖ :=
        (norm_sph_bigCell _ _).symm
    _ ≤ C := hC _ hmem

theorem exists_bound_sphSum_siegel (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ)) {s : ℂ} (hs : 1 / 2 < s.re) (c u : ℝ)
    (hc : 0 < c) :
    ∃ C : ℝ, ∀ g ∈ integralWindowedSiegelSet F c u, sphSum F s g ≤ C := by
  obtain ⟨T₀, C₁, h₁⟩ := exists_bound_sphSum_high hα hs c u hc
  obtain ⟨C₂, h₂⟩ := exists_bound_sphSum_low hα hs c u T₀ hc
  refine ⟨max C₁ C₂, fun g hg => ?_⟩
  by_cases hT : T₀ < archHeight F (glArch (𝓞 F) F g)
  · exact (h₁ g hg hT).trans (le_max_left _ _)
  · exact (h₂ g hg (not_lt.1 hT)).trans (le_max_right _ _)

end SiegelBound

section Slab

variable {F}

theorem nullMeasurableSet_of_restrict {X : Type*} [MeasurableSpace X] (μ : Measure X) {s t : Set X}
    (ht : MeasurableSet t) (hst : s ⊆ t) (h : NullMeasurableSet s (μ.restrict t)) : NullMeasurableSet s μ := by
  obtain ⟨s', hs'm, hs'⟩ := h
  refine ⟨s' ∩ t, hs'm.inter ht, ?_⟩
  have h2 : ∀ᵐ x ∂μ, x ∈ t → (x ∈ s) = (x ∈ s') := (ae_restrict_iff' ht).mp hs'
  filter_upwards [h2] with x hx
  by_cases hxt : x ∈ t
  · have := hx hxt
    show (x ∈ s) = (x ∈ s' ∩ t)
    rw [this]; simp [hxt]
  · have hxs : x ∉ s := fun h => hxt (hst h)
    show (x ∈ s) = (x ∈ s' ∩ t)
    simp [hxs, hxt]

variable (F) in

def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab F α β) :=
  measurableSet_preimage (NumberField.TateGlobal.continuous_ideleNorm_det F).measurable measurableSet_Icc

theorem nullMeasurableSet_and_measure_lt_top_of_isFundamentalDomain_slab {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    {Φ : Set (AdelicGL2 (𝓞 F) F)} (hΦs : Φ ⊆ slab F α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β))) :
    NullMeasurableSet Φ (adelicGLHaar (Fin 2) (𝓞 F) F) ∧ adelicGLHaar (Fin 2) (𝓞 F) F Φ < ⊤ := by
  refine ⟨nullMeasurableSet_of_restrict _ (measurableSet_slab α β) hΦs hΦ.nullMeasurableSet, ?_⟩
  have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
    F α β hα hαβ Φ hΦ
  rwa [Set.inter_eq_self_of_subset_left (show Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F
    (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} from hΦs)] at h

end Slab

section Measurability

variable {F}

scoped instance isFiniteMeasure_cond_adelicBox :
    IsFiniteMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  haveI := isProbabilityMeasure_cond_adelicBox F
  infer_instance

theorem continuous_pseudoEisenstein (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    {s : ℂ} (hs : 1 / 2 < s.re) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) φ) (hφc : Continuous φ) :
    Continuous (pseudoEisenstein F φ) := by
  rw [pseudoEisenstein_eq]
  exact hφc.add (AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half F hα μ ν hμ hν s hs φ hφ hφc)

theorem measurable_lambdaT_pseudoEisenstein (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    {s : ℂ} (hs : 1 / 2 < s.re) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) φ) (hφc : Continuous φ) (T : ℝ) :
    Measurable (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => unipotentGL2 t) (adelicHeight F) T (pseudoEisenstein F φ)) := by
  have hE := continuous_pseudoEisenstein hα hμ hν hs hφ hφc
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have hCT : StronglyMeasurable (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => unipotentGL2 t) (pseudoEisenstein F φ)) := by
    have hc2 : Continuous fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F =>
        pseudoEisenstein F φ (unipotentGL2 p.2 * p.1) :=
      hE.comp ((AutomorphicForm.continuous_unipotentGL2.comp continuous_snd).mul continuous_fst)
    have h := hc2.stronglyMeasurable
    exact h.integral_prod_right'
  have hH : MeasurableSet (highSet (adelicHeight F) T) :=
    measurableSet_lt measurable_const (NumberField.AdelicHeight.continuous_adelicHeight F).measurable
  exact hE.measurable.sub (hCT.measurable.indicator hH)

end Measurability

section Main

variable {F}

theorem norm_add_sub_add_left (a b c : ℂ) : ‖a + b - (a + c)‖ = ‖b - c‖ := by
  congr 1; ring

theorem memLp_two_lambdaT_pseudoEisenstein (α β : ℝ) (hαpos : 0 < α) (hαβ : α < β)
    (hα : ∀ x, 0 < ((αF x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    {s : ℂ} (hs : 1 / 2 < s.re) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) φ) (hφc : Continuous φ) (R : ℝ) :
    MemLp (lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t)
        (adelicHeight F) (Real.exp R) (pseudoEisenstein F φ)) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (canonicalTruncationDomain F α β)) := by

  obtain ⟨hc0, hTc, hcover, hslab, hfd⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum F α β hαpos hαβ
  set c₀ := canonicalTruncationFloor F α β with hc₀def
  set u₀ := canonicalTruncationWindow F α β with hu₀def
  set d₁ := canonicalTruncationLowerCut F α β with hd₁def
  set d₂ := canonicalTruncationUpperCut F α β with hd₂def
  set Tc := canonicalTruncationTranslates F α β with hTcdef
  set Φ₀ := canonicalTruncationDomain F α β with hΦ₀def
  set c' : ℝ := c₀ ^ (∑ w : InfinitePlace F, w.mult) with hc'def
  have hc'pos : 0 < c' := pow_pos hc0 _
  have hSD : centreCutSiegelSet F c₀ u₀ d₁ d₂ ⊆ integralWindowedSiegelSet F c' u₀ :=
    centreCutSiegelSet_subset_integralWindowedSiegelSet hc0.le

  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_bound_on_maximalCompact_mul hφc (isCompact_singleton (x := (1 : AdelicGL2 (𝓞 F) F)))
  have hC₀' : ∀ k ∈ adelicMaximalCompact F, ‖φ k‖ ≤ C₀ := fun k hk => by
    simpa using hC₀ k hk 1 rfl
  obtain ⟨C, hCnn, hC⟩ := exists_bound_on_maximalCompact_mul hφc hTc
  obtain ⟨CD, hCD⟩ := exists_bound_sphSum_siegel hα hs c' u₀ hc'pos
  set κ : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ with hκ
  set Cfin : ℝ := C₀ * Real.exp R ^ (s.re + 1 / 2) + C * CD + ‖κ‖ * (C * sphInt F s * c' ^ (1 / 2 - s.re))
    with hCfin
  have hpos1 : 0 ≤ C₀ * Real.exp R ^ (s.re + 1 / 2) := mul_nonneg hC₀0 (Real.rpow_nonneg (Real.exp_pos R).le _)
  have hpos3 : 0 ≤ ‖κ‖ * (C * sphInt F s * c' ^ (1 / 2 - s.re)) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg hCnn (sphInt_nonneg s)) (Real.rpow_nonneg hc'pos.le _))

  have hbound : ∀ x ∈ Φ₀, ‖lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => unipotentGL2 t) (adelicHeight F) (Real.exp R) (pseudoEisenstein F φ) x‖ ≤ Cfin := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
    obtain ⟨g, hg, hgx⟩ := hxy
    have hgD := hSD hg
    have hxeq : x = g * y := hgx.symm

    have hφy : IsInducedSection (𝓞 F) F (etaFst μ αF hα s) (etaSnd ν αF hα s) (fun h => φ (h * y)) :=
      hφ.rightTranslate y
    have hφyc : Continuous fun h => φ (h * y) := continuous_rightTranslate hφc y
    have hCy : ∀ k ∈ adelicMaximalCompact F, ‖(fun h => φ (h * y)) k‖ ≤ C := fun k hk => hC k hk y hy

    have hT : ‖bigCell F φ x‖ ≤ C * CD := by
      have e : bigCell F φ x = bigCell F (fun h => φ (h * y)) g := by
        rw [hxeq]
        unfold bigCell
        exact tsum_congr fun ξ => by simp only [mul_assoc]
      rw [e]
      exact (norm_bigCell_le hα hμ hν hs hφy hφyc hCy g).trans (mul_le_mul_of_nonneg_left (hCD g hgD) hCnn)

    have hM : ‖weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ x‖
        ≤ C * sphInt F s * c' ^ (1 / 2 - s.re) := by
      have e : weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ x
          = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (fun h => φ (h * y)) g := by
        rw [hxeq]
        unfold weylIntertwiningIntegral
        simp only [mul_assoc]
      rw [e]
      refine (norm_weylIntertwiningIntegral_le hα hμ hν hs hφy hφyc hCnn hCy g).trans ?_
      have hHg : c' ≤ adelicHeight F g := by
        rw [adelicHeight_eq_archHeight_of_mem hgD.1]
        exact hgD.2.1
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc'pos hHg (by linarith))
        (mul_nonneg hCnn (sphInt_nonneg s))

    have hφx : ‖φ x‖ ≤ C₀ * adelicHeight F x ^ (s.re + 1 / 2) := norm_apply_le_gauge hα hμ hν s hφ hC₀' x

    by_cases hhigh : Real.exp R < adelicHeight F x
    · rw [lambdaT_apply_of_lt _ _ hhigh]
      have hCT := AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hα μ ν
        hμ hν s hs φ hφ hφc x
      change constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun t => unipotentGL2 t)
          (pseudoEisenstein F φ) x
          = φ x + κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ x at hCT
      rw [hCT, pseudoEisenstein_eq]
      calc ‖φ x + bigCell F φ x - (φ x + κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ x)‖
          = ‖bigCell F φ x - κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ x‖ :=
            norm_add_sub_add_left _ _ _
        _ ≤ ‖bigCell F φ x‖ + ‖κ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ x‖ :=
            norm_sub_le _ _
        _ ≤ C * CD + ‖κ‖ * (C * sphInt F s * c' ^ (1 / 2 - s.re)) := by
            refine add_le_add hT ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left hM (norm_nonneg _)
        _ ≤ Cfin := by rw [hCfin]; linarith
    · have hle : adelicHeight F x ≤ Real.exp R := not_lt.1 hhigh
      rw [lambdaT_apply_of_le _ _ hle, pseudoEisenstein_eq]
      calc ‖φ x + bigCell F φ x‖ ≤ ‖φ x‖ + ‖bigCell F φ x‖ := norm_add_le _ _
        _ ≤ C₀ * Real.exp R ^ (s.re + 1 / 2) + C * CD := by
            refine add_le_add (hφx.trans ?_) hT
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (adelicHeight_pos x).le hle (by linarith)) hC₀0
        _ ≤ Cfin := by rw [hCfin]; linarith

  obtain ⟨hnull, hfin⟩ := nullMeasurableSet_and_measure_lt_top_of_isFundamentalDomain_slab hαpos hαβ hslab hfd
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := isFiniteMeasure_restrict.2 hfin.ne
  refine MemLp.of_bound (measurable_lambdaT_pseudoEisenstein hα hμ hν hs hφ hφc (Real.exp R)).aestronglyMeasurable
    Cfin ?_
  rw [ae_restrict_iff'₀ hnull]
  exact Filter.Eventually.of_forall hbound

end Main

end R1L2Trunc
p2m_reactivate "P2MW.S_AutomorphicForm_memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain.R1L2Trunc"

end
p2m_reactivate "P2MW.S_AutomorphicForm_memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain.R1L2Trunc"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar in
open IsDedekindDomain in
open AutomorphicForm in
open scoped NNReal in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ)
      (R : ℝ),
    MemLp (fun x : AdelicGL2 (𝓞 F) F =>
      @AutomorphicForm.lambdaT _
        (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
        (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
        (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
        (AutomorphicForm.pseudoEisenstein F φ) x) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (AutomorphicForm.canonicalTruncationDomain F α β)) := by
  intro αm hαm μ ν hμ hν s hs φ hφ hφc _hφK _hφf R
  exact R1L2Trunc.memLp_two_lambdaT_pseudoEisenstein α β hα hαβ hαm hμ hν hs hφ hφc R

end S_AutomorphicForm_memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain (solution)
