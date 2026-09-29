-- Prove2me | solution 1 for AutomorphicForm.ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8bad0f51-c812-500b-943c-50f9fb28e48c

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_ResidualSpan
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_lsXi_threeWay_orthogonal_decomposition_haar_ae_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_ae_constantTerm_eq_zero_of_mem_residualSpan_slab
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
import Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab
import Theorems.Thm_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab
import Theorems.Thm_AutomorphicForm_ae_constantTerm_eq_zero_of_ae_eq_restrict_slab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

open AutomorphicForm
open scoped ENNReal ComplexConjugate

namespace CuspidalOrthogonality

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

private theorem memLp_conj {u : X → ℂ} (hu : MemLp u 2 m) : MemLp (fun x => conj (u x)) 2 m := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hu.1, ?_⟩
  have h : eLpNorm (fun x => conj (u x)) 2 m = eLpNorm u 2 m :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => Complex.norm_conj (u x))
  rw [h]
  exact hu.2

private theorem integrable_mul_conj {v u : X → ℂ} (hv : MemLp v 2 m) (hu : MemLp u 2 m) :
    Integrable (fun x => v x * conj (u x)) m :=
  memLp_one_iff_integrable.mp ((memLp_conj hu).mul' (r := 1) hv)

private theorem enorm_integral_mul_conj_le {v u : X → ℂ} (hv : AEStronglyMeasurable v m)
    (hu : AEStronglyMeasurable u m) :
    ‖∫ x, v x * conj (u x) ∂m‖ₑ ≤ eLpNorm v 2 m * eLpNorm (fun x => conj (u x)) 2 m :=
  calc ‖∫ x, v x * conj (u x) ∂m‖ₑ
      ≤ ∫⁻ x, ‖v x * conj (u x)‖ₑ ∂m := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (v • fun x => conj (u x)) 1 m :=
        (eLpNorm_one_eq_lintegral_enorm (f := v • fun x => conj (u x))).symm
    _ ≤ eLpNorm v 2 m * eLpNorm (fun x => conj (u x)) 2 m :=
        eLpNorm_smul_le_mul_eLpNorm (Complex.continuous_conj.comp_aestronglyMeasurable hu) hv

private theorem integral_mul_conj_eq_zero_of_forall_exists_eLpNorm_sub_lt {v u : X → ℂ} (hv : MemLp v 2 m)
    (hu : MemLp u 2 m)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ r : X → ℂ, MemLp r 2 m ∧ (∫ x, r x * conj (u x) ∂m) = 0 ∧
      eLpNorm (v - r) 2 m < ENNReal.ofReal ε) :
    ∫ x, v x * conj (u x) ∂m = 0 := by
  have hSfin : eLpNorm (fun x => conj (u x)) 2 m ≠ ∞ := (memLp_conj hu).eLpNorm_ne_top
  have key : ∀ ε : ℝ, 0 < ε →
      ‖∫ x, v x * conj (u x) ∂m‖ ≤ ε * (eLpNorm (fun x => conj (u x)) 2 m).toReal := by
    intro ε hε
    obtain ⟨r, hr, hr0, hvr⟩ := happrox ε hε
    have hsplit : ∫ x, (v - r) x * conj (u x) ∂m = ∫ x, v x * conj (u x) ∂m := by
      have h1 : ∫ x, (v - r) x * conj (u x) ∂m
          = ∫ x, v x * conj (u x) ∂m - ∫ x, r x * conj (u x) ∂m := by
        rw [← integral_sub (integrable_mul_conj hv hu) (integrable_mul_conj hr hu)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show (v - r) x * conj (u x) = v x * conj (u x) - r x * conj (u x)
        rw [Pi.sub_apply, sub_mul]
      rw [h1, hr0, sub_zero]
    have hbound := enorm_integral_mul_conj_le (hv.sub hr).1 hu.1
    rw [hsplit] at hbound
    have hle : ‖∫ x, v x * conj (u x) ∂m‖ₑ
        ≤ ENNReal.ofReal ε * eLpNorm (fun x => conj (u x)) 2 m :=
      hbound.trans (mul_le_mul' hvr.le le_rfl)
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin) hle
    rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le] at hreal
    exact hreal
  by_contra hne
  have hpos : 0 < ‖∫ x, v x * conj (u x) ∂m‖ := norm_pos_iff.mpr hne
  obtain ⟨ε, hε, hεlt⟩ := exists_pos_mul_lt hpos (eLpNorm (fun x => conj (u x)) 2 m).toReal
  have hkey := key ε hε
  rw [mul_comm] at hkey
  exact lt_irrefl _ (hkey.trans_lt hεlt)

private theorem integral_mul_conj_swap_eq_zero {a b : X → ℂ} (h : ∫ x, a x * conj (b x) ∂m = 0) :
    ∫ x, b x * conj (a x) ∂m = 0 := by
  have hc : ∫ x, b x * conj (a x) ∂m = conj (∫ x, a x * conj (b x) ∂m) := by
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show b x * conj (a x) = conj (a x * conj (b x))
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [hc, h, map_zero]

private theorem integral_add_mul_conj_eq_zero {v₁ v₂ u : X → ℂ} (hv₁ : MemLp v₁ 2 m) (hv₂ : MemLp v₂ 2 m)
    (hu : MemLp u 2 m) (h₁ : ∫ x, v₁ x * conj (u x) ∂m = 0) (h₂ : ∫ x, v₂ x * conj (u x) ∂m = 0) :
    ∫ x, (v₁ + v₂) x * conj (u x) ∂m = 0 := by
  have h : ∫ x, (v₁ + v₂) x * conj (u x) ∂m
      = ∫ x, v₁ x * conj (u x) ∂m + ∫ x, v₂ x * conj (u x) ∂m := by
    rw [← integral_add (integrable_mul_conj hv₁ hu) (integrable_mul_conj hv₂ hu)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (v₁ + v₂) x * conj (u x) = v₁ x * conj (u x) + v₂ x * conj (u x)
    rw [Pi.add_apply, add_mul]
  rw [h, h₁, h₂, add_zero]

private theorem ae_eq_zero_of_forall_exists_integral_mul_conj_eq_zero_and_eLpNorm_sub_lt {g : X → ℂ}
    (hg : MemLp g 2 m)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ θ : X → ℂ, MemLp θ 2 m ∧ (∫ x, θ x * conj (g x) ∂m) = 0 ∧
      eLpNorm (g - θ) 2 m < ENNReal.ofReal ε) :
    g =ᵐ[m] 0 := by
  have hself : ∫ x, g x * conj (g x) ∂m = 0 :=
    integral_mul_conj_eq_zero_of_forall_exists_eLpNorm_sub_lt hg hg happrox
  have hsq : ∫ x, ‖g x‖ ^ 2 ∂m = 0 := by
    have h : ∫ x, g x * conj (g x) ∂m = ((∫ x, ‖g x‖ ^ 2 ∂m : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show g x * conj (g x) = ((‖g x‖ ^ 2 : ℝ) : ℂ)
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h] at hself
    exact_mod_cast hself
  have hint : Integrable (fun x => ‖g x‖ ^ 2) m := (memLp_two_iff_integrable_sq_norm hg.1).mp hg
  have h0 : (fun x => ‖g x‖ ^ 2) =ᵐ[m] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖g x‖) hint).mp hsq
  filter_upwards [h0] with x hx
  have hx' : ‖g x‖ ^ 2 = 0 := hx
  simpa using hx'

private theorem ae_eq_left_of_forall_exists_eLpNorm_sub_lt {f fc g : X → ℂ} (hfc : MemLp fc 2 m)
    (hg : MemLp g 2 m) (hdecomp : f =ᵐ[m] fc + g)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ θ : X → ℂ, MemLp θ 2 m ∧ (∫ x, θ x * conj (f x) ∂m) = 0 ∧
      (∫ x, θ x * conj (fc x) ∂m) = 0 ∧ eLpNorm (g - θ) 2 m < ENNReal.ofReal ε) :
    f =ᵐ[m] fc := by
  have hg0 : g =ᵐ[m] 0 := by
    refine ae_eq_zero_of_forall_exists_integral_mul_conj_eq_zero_and_eLpNorm_sub_lt hg ?_
    intro ε hε
    obtain ⟨θ, hθ, hθf, hθc, hgθ⟩ := happrox ε hε
    refine ⟨θ, hθ, ?_, hgθ⟩
    have h1 : ∫ x, θ x * conj (f x) ∂m
        = ∫ x, θ x * conj (fc x) ∂m + ∫ x, θ x * conj (g x) ∂m := by
      rw [← integral_add (integrable_mul_conj hθ hfc) (integrable_mul_conj hθ hg)]
      refine integral_congr_ae ?_
      filter_upwards [hdecomp] with x hx
      rw [hx, Pi.add_apply, map_add, mul_add]
    rw [hθf, hθc, zero_add] at h1
    exact h1.symm
  filter_upwards [hdecomp, hg0] with x hx hx0
  simp [hx, hx0]

section OrbitSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

private theorem setIntegral_out_mul_conj_out_eq_zero (μ : Measure G) (H : Subgroup G) (μH : Measure H)
    (S : Set (MulAction.orbitRel.Quotient H G)) (φ c : G → ℂ)
    (hinv : ∀ h ∈ H, ∀ g : G, c (h * g) = c g) (hc : ∀ᵐ g ∂μ, c g = 0) :
    ∫ q in S, φ q.out * starRingEnd ℂ (c q.out) ∂(HaarQuotient.measure μ H μH) = 0 := by
  have hout : ∀ g : G, c (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = c g := by
    intro g
    have hmem : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ∈ MulAction.orbit H g :=
      MulAction.orbitRel_apply.mp (Quotient.mk_out' (s₁ := MulAction.orbitRel H G) g)
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp hmem
    have hx' : (x : G) * g = (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out := hx
    rw [← hx']
    exact hinv x x.2 g
  have hlin : ∫⁻ q, ‖φ q.out * starRingEnd ℂ (c q.out)‖ₑ ∂((HaarQuotient.measure μ H μH).restrict S)
      = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ q, ‖φ q.out * starRingEnd ℂ (c q.out)‖ₑ ∂((HaarQuotient.measure μ H μH).restrict S)
        ≤ ∫⁻ q, ‖φ q.out * starRingEnd ℂ (c q.out)‖ₑ ∂(HaarQuotient.measure μ H μH) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ q, ‖φ q.out * starRingEnd ℂ (c q.out)‖ₑ
            ∂(Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
              (μ.withDensity (HaarQuotient.density H μH))) := rfl
      _ ≤ ∫⁻ g, ‖φ (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out
            * starRingEnd ℂ (c (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out)‖ₑ
            ∂(μ.withDensity (HaarQuotient.density H μH)) :=
          lintegral_map_le _ _
      _ = ∫⁻ _g, (0 : ℝ≥0∞) ∂(μ.withDensity (HaarQuotient.density H μH)) := by
          refine lintegral_congr_ae ?_
          have hc' : ∀ᵐ g ∂(μ.withDensity (HaarQuotient.density H μH)), c g = 0 :=
            (withDensity_absolutelyContinuous μ (HaarQuotient.density H μH)).ae_le hc
          filter_upwards [hc'] with g hg
          rw [hout g, hg, map_zero, mul_zero, enorm_zero]
      _ = 0 := lintegral_zero
  have hle := enorm_integral_le_lintegral_enorm (μ := (HaarQuotient.measure μ H μH).restrict S)
    (fun q : MulAction.orbitRel.Quotient H G => φ q.out * starRingEnd ℂ (c q.out))
  rw [hlin, nonpos_iff_eq_zero, enorm_eq_zero] at hle
  exact hle

end OrbitSpace

section Invariance

variable (F : Type) [Field F] [NumberField F]

private def leftInvariantSubgroup (c : AdelicGL2 (𝓞 F) F → ℂ) : Subgroup (AdelicGL2 (𝓞 F) F) where
  carrier := {h | ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g}
  one_mem' := by
    intro g
    rw [one_mul]
  mul_mem' := by
    intro a b ha hb
    have ha' : ∀ g : AdelicGL2 (𝓞 F) F, c (a * g) = c g := ha
    have hb' : ∀ g : AdelicGL2 (𝓞 F) F, c (b * g) = c g := hb
    intro g
    rw [mul_assoc, ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : ∀ g : AdelicGL2 (𝓞 F) F, c (a * g) = c g := ha
    intro g
    have h := ha' (a⁻¹ * g)
    rw [mul_inv_cancel_left] at h
    exact h.symm

private theorem mem_leftInvariantSubgroup {c : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F} :
    h ∈ leftInvariantSubgroup F c ↔ ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g :=
  Iff.rfl

omit [NumberField F] in

private theorem scalar_mem_borelSubgroup (a : Fˣ) :
    Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a ∈ borelSubgroup F := by
  show ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  have hval : ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (a : F) := rfl
  rw [hval, Matrix.scalar_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

omit [NumberField F] in

private theorem diagOne_mem_borelSubgroup (a : Fˣ) : diagOne a ∈ borelSubgroup F := by
  show ((diagOne a : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  rw [diagOne_coe_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

private theorem forall_mem_rationalTorusUnipotent_mul_eq (c : AdelicGL2 (𝓞 F) F → ℂ)
    (hN : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), c (unipotentGL2 x * g) = c g)
    (hB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, c (globalPoints (𝓞 F) F γ * g) = c g) :
    ∀ h ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g := by
  have hle : rationalTorusUnipotent F ≤ leftInvariantSubgroup F c := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨a, rfl⟩ g
      exact hB _ (scalar_mem_borelSubgroup F a) g
    · rintro _ ⟨a, rfl⟩ g
      exact hB _ (diagOne_mem_borelSubgroup F a) g
    · rintro _ ⟨x, rfl⟩ g
      exact hN x.toAdd g
  intro h hh g
  have hmem : h ∈ leftInvariantSubgroup F c := hle hh
  exact (mem_leftInvariantSubgroup F).mp hmem g

private abbrev pinsAt (Φ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private theorem constantTerm_rationalTorusUnipotent_mul (Φ : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (pinsAt F Φ).Z →* ℂˣ) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsAutomorphicFnAt F (pinsAt F Φ) ξ f) :
    letI := (pinsAt F Φ).nS
    ∀ h ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      constantTerm (pinsAt F Φ).ν unipotentGL2 f (h * g) = constantTerm (pinsAt F Φ).ν unipotentGL2 f g := by
  have hls : IsLsXiFunction (𝓞 F) F (pinsAt F Φ).Z ξ f := by
    letI := (pinsAt F Φ).mS
    exact ((lsXiMemberAt_iff (𝓞 F) F (pinsAt F Φ).μ (pinsAt F Φ).Z ξ (pinsAt F Φ).D f).mp hf).1
  have hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      f (globalPoints (𝓞 F) F γ * g) = f g := hls.left_invariant
  letI := (pinsAt F Φ).nS
  refine forall_mem_rationalTorusUnipotent_mul_eq F (constantTerm (pinsAt F Φ).ν unipotentGL2 f) ?_ ?_
  · intro x g
    exact constantTerm_adelicBox_unipotentGL2_mul F (fun k h => hleft (unipotentGL2 k) h) x g
  · intro γ hγ g
    exact constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup F (fun γ' _ h => hleft γ' h) hγ g

private theorem setIntegral_slabQuotient_eq_zero_of_ae_constantTerm_eq_zero (d₁ d₂ : ℝ)
    (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pinsAt F Φ).Z →* ℂˣ) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsAutomorphicFnAt F (pinsAt F Φ) ξ f)
    (hcusp : letI := (pinsAt F Φ).mS
      letI := (pinsAt F Φ).nS
      ∀ᵐ g ∂(pinsAt F Φ).μ, constantTerm (pinsAt F Φ).ν unipotentGL2 f g = 0)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    letI := (pinsAt F Φ).mS
    letI := (pinsAt F Φ).nS
    ∫ q in {q : RationalTorusUnipotentQuotient F |
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂},
        φ q.out * starRingEnd ℂ (constantTerm (pinsAt F Φ).ν unipotentGL2 f q.out)
      ∂(rationalTorusUnipotentQuotientMeasure F) = 0 :=
  setIntegral_out_mul_conj_out_eq_zero (pinsAt F Φ).μ (rationalTorusUnipotent F)
    (rationalTorusUnipotentHaar F) _ φ _ (constantTerm_rationalTorusUnipotent_mul F Φ ξ f hf) hcusp

end Invariance

section Assembly

variable (F : Type) [Field F] [NumberField F]

private theorem memLp_two_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pinsAt F Φ).Z →* ℂˣ)
    {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : IsAutomorphicFnAt F (pinsAt F Φ) ξ v) :
    letI := (pinsAt F Φ).mS
    MemLp v 2 ((pinsAt F Φ).μ.restrict (pinsAt F Φ).D) := by
  letI := (pinsAt F Φ).mS
  exact ((lsXiMemberAt_iff (𝓞 F) F (pinsAt F Φ).μ (pinsAt F Φ).Z ξ (pinsAt F Φ).D v).mp hv).2

private theorem isAutomorphicFnAt_add_of (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pinsAt F Φ).Z →* ℂˣ)
    {v w : AdelicGL2 (𝓞 F) F → ℂ} (hv : IsAutomorphicFnAt F (pinsAt F Φ) ξ v)
    (hw : IsAutomorphicFnAt F (pinsAt F Φ) ξ w) : IsAutomorphicFnAt F (pinsAt F Φ) ξ (v + w) := by
  letI := (pinsAt F Φ).mS
  obtain ⟨hv₁, hv₂⟩ := (lsXiMemberAt_iff (𝓞 F) F (pinsAt F Φ).μ (pinsAt F Φ).Z ξ (pinsAt F Φ).D v).mp hv
  obtain ⟨hw₁, hw₂⟩ := (lsXiMemberAt_iff (𝓞 F) F (pinsAt F Φ).μ (pinsAt F Φ).Z ξ (pinsAt F Φ).D w).mp hw
  refine (lsXiMemberAt_iff (𝓞 F) F (pinsAt F Φ).μ (pinsAt F Φ).Z ξ (pinsAt F Φ).D (v + w)).mpr
    ⟨⟨?_, ?_⟩, hv₂.add hw₂⟩
  · intro γ g
    simp only [Pi.add_apply, hv₁.left_invariant γ g, hw₁.left_invariant γ g]
  · intro z g
    simp only [Pi.add_apply, hv₁.central_transform z g, hw₁.central_transform z g, mul_add]

end Assembly

end CuspidalOrthogonality

open CuspidalOrthogonality

theorem solution
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (hξ : Continuous ξ)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (_hf : IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ f) :
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS
    (∀ᵐ g ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ,
        constantTerm (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).ν unipotentGL2 f g = 0) ↔
      ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, AutomorphicForm.IsSlabProfile F
          (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ →
        ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
            AutomorphicForm.pseudoEisenstein F φ g * starRingEnd ℂ (f g)
          ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ = 0 := by
  refine ⟨fun hcusp φ hφ => ?_, fun horth => ?_⟩
  ·

    exact Eq.trans
      (AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab
        F d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ ξ f _hf φ hφ)
      (setIntegral_slabQuotient_eq_zero_of_ae_constantTerm_eq_zero F d₁ d₂ Φ ξ f _hf hcusp φ)
  ·
    have hdecomp₀ :=
      AutomorphicForm.lsXi_threeWay_orthogonal_decomposition_haar_ae_of_isFundamentalDomain_slab
        F d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ ξ f _hf
    obtain ⟨fc, fr, fe, ⟨hfc, hfccusp⟩, ⟨hfr, hfrapprox⟩, ⟨hfe, hfeperp⟩, hdecomp⟩ := hdecomp₀
    have hg : IsAutomorphicFnAt F (pinsAt F Φ) ξ (fr + fe) := isAutomorphicFnAt_add_of F Φ ξ hfr hfe

    have hfcf := ae_eq_left_of_forall_exists_eLpNorm_sub_lt (f := f) (memLp_two_of_isAutomorphicFnAt F Φ ξ hfc)
      (memLp_two_of_isAutomorphicFnAt F Φ ξ hg) (by rw [← add_assoc]; exact hdecomp) (fun ε hε => by
        have happrox :=
          AutomorphicForm.exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab
            F d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ ξ hξ (fr + fe) hg (fun u hu hucusp => by
              have hfe_u := hfeperp u hu (Or.inl hucusp)
              have hfr_u := integral_mul_conj_eq_zero_of_forall_exists_eLpNorm_sub_lt
                (memLp_two_of_isAutomorphicFnAt F Φ ξ hfr) (memLp_two_of_isAutomorphicFnAt F Φ ξ hu)
                (fun δ hδ => by
                  obtain ⟨r, hrmem, hrauto, hrclose⟩ := hfrapprox δ hδ
                  refine ⟨r, memLp_two_of_isAutomorphicFnAt F Φ ξ hrauto, ?_, hrclose⟩
                  exact integral_mul_conj_swap_eq_zero
                    (AutomorphicForm.setIntegral_mul_conj_eq_zero_of_ae_constantTerm_eq_zero_of_mem_residualSpan_slab
                      F d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ ξ u hu hucusp r hrauto hrmem))
              exact integral_add_mul_conj_eq_zero (memLp_two_of_isAutomorphicFnAt F Φ ξ hfr)
                (memLp_two_of_isAutomorphicFnAt F Φ ξ hfe) (memLp_two_of_isAutomorphicFnAt F Φ ξ hu) hfr_u hfe_u)
            ε hε
        obtain ⟨φ, hφ, hclose⟩ := happrox
        refine ⟨AutomorphicForm.pseudoEisenstein F φ, memLp_two_of_isAutomorphicFnAt F Φ ξ
          (AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab F d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ ξ φ hφ),
          horth φ hφ, ?_, hclose⟩
        exact Eq.trans
          (AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab
            F d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ ξ fc hfc φ hφ)
          (setIntegral_slabQuotient_eq_zero_of_ae_constantTerm_eq_zero F d₁ d₂ Φ ξ fc hfc hfccusp φ))

    exact AutomorphicForm.ae_constantTerm_eq_zero_of_ae_eq_restrict_slab F d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ ξ fc f hfc _hf
      hfcf.symm hfccusp

end

end S_AutomorphicForm_ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab
end P2MW
export P2MW.S_AutomorphicForm_ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab (solution)
