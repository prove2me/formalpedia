-- Prove2me | solution 1 for AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/99a45c02-9f43-5310-a580-f5555e1fe820

import Mathlib
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_integral_mul_conj_weylIntertwiningIntegral_eq_integral_weylIntertwiningIntegral_mul_conj_of_re_gt_half
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family
import Theorems.Thm_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
p2m_attr_erase "instance" "FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.fnTwist_zero"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.preimage_mulLeft_smul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel

noncomputable section

namespace R4AdjAxis

section Topology

open Metric Set

theorem isPreconnected_ball_diff_center (c : ℂ) (r : ℝ) :
    IsPreconnected (ball c r \ {c}) := by
  let P : ℝ × ℝ → ℂ := fun p => c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  have hP : Continuous P := by
    unfold P; fun_prop
  have himg : P '' (Ioo (0 : ℝ) r ×ˢ (univ : Set ℝ)) = ball c r \ {c} := by
    ext z
    constructor
    · rintro ⟨⟨ρ, θ⟩, ⟨⟨hρ0, hρr⟩, -⟩, rfl⟩
      have hnorm : ‖(ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = ρ := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hρ0]
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm]
        simp only [P, add_sub_cancel_left, hnorm]
        exact hρr
      · intro hz
        rw [mem_singleton_iff] at hz
        have : (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = 0 := by
          have h1 : P (ρ, θ) - c = 0 := by rw [hz, sub_self]
          simpa [P] using h1
        have h2 : ‖(ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = 0 := by rw [this, norm_zero]
        rw [hnorm] at h2
        exact absurd h2 hρ0.ne'
    · rintro ⟨hz, hzc⟩
      rw [mem_singleton_iff] at hzc
      have hu : z - c ≠ 0 := sub_ne_zero.mpr hzc
      refine ⟨(‖z - c‖, (z - c).arg), ⟨⟨norm_pos_iff.mpr hu, ?_⟩, mem_univ _⟩, ?_⟩
      · rwa [mem_ball, dist_eq_norm] at hz
      · simp only [P]
        rw [Complex.norm_mul_exp_arg_mul_I (z - c)]
        ring
  rw [← himg]
  exact ((isPreconnected_Ioo).prod isPreconnected_univ).image _ hP.continuousOn

theorem isPreconnected_diff_singleton {V : Set ℂ} (hVo : IsOpen V) (hV : IsPreconnected V) (c : ℂ) :
    IsPreconnected (V \ {c}) := by
  by_cases hcV : c ∈ V
  swap
  · rwa [diff_singleton_eq_self hcV]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVo c hcV
  have hD : IsPreconnected (ball c r \ {c}) := isPreconnected_ball_diff_center c r
  have hDsub : ball c r \ {c} ⊆ V \ {c} := diff_subset_diff_left hball

  have key : ∀ u v : Set ℂ, IsOpen u → IsOpen v → V \ {c} ⊆ u ∪ v → (V \ {c}) ∩ (u ∩ v) = ∅ →
      ((V \ {c}) ∩ v).Nonempty → ball c r \ {c} ⊆ u → False := by
    intro u v hu hv hsub hempty hne hDu
    have hne' : (V ∩ (u ∪ ball c r)).Nonempty := ⟨c, hcV, Or.inr (mem_ball_self hr)⟩
    have hneV : (V ∩ v).Nonempty := by
      obtain ⟨b, hb, hbv⟩ := hne
      exact ⟨b, hb.1, hbv⟩
    have hcover : V ⊆ (u ∪ ball c r) ∪ v := by
      intro x hx
      by_cases hxc : x = c
      · exact Or.inl (Or.inr (by rw [hxc]; exact mem_ball_self hr))
      · rcases hsub ⟨hx, hxc⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    obtain ⟨x, hxV, hxu, hxv⟩ := hV _ _ (hu.union isOpen_ball) hv hcover hne' hneV
    by_cases hxc : x = c
    ·
      subst hxc
      obtain ⟨ε, hε, hεv⟩ := Metric.isOpen_iff.mp hv x hxv
      set δ : ℝ := min ε r / 2 with hδ
      have hδpos : 0 < δ := by rw [hδ]; positivity
      have hδε : δ < ε := by
        rw [hδ]; linarith [min_le_left ε r]
      have hδr : δ < r := by
        rw [hδ]; linarith [min_le_right ε r]
      set y : ℂ := x + (δ : ℂ) with hy
      have hdist : dist y x = δ := by
        rw [dist_eq_norm, hy, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
      have hyD : y ∈ ball x r \ {x} := by
        refine ⟨by rw [mem_ball, hdist]; exact hδr, ?_⟩
        intro h
        rw [mem_singleton_iff] at h
        have : dist y x = 0 := by rw [h, dist_self]
        rw [hdist] at this
        exact absurd this hδpos.ne'
      have hyv : y ∈ v := hεv (by rw [mem_ball, hdist]; exact hδε)
      have : y ∈ (V \ {x}) ∩ (u ∩ v) := ⟨hDsub hyD, hDu hyD, hyv⟩
      rw [hempty] at this
      exact this
    · have hxW : x ∈ V \ {c} := ⟨hxV, hxc⟩
      have hxu' : x ∈ u := by
        rcases hxu with h | h
        · exact h
        · exact hDu ⟨h, hxc⟩
      have : x ∈ (V \ {c}) ∩ (u ∩ v) := ⟨hxW, hxu', hxv⟩
      rw [hempty] at this
      exact this
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsub hempty
  by_contra hcon
  push Not at hcon
  obtain ⟨hnu, hnv⟩ := hcon
  obtain ⟨a, haW, hau⟩ := not_subset.mp hnu
  obtain ⟨b, hbW, hbv⟩ := not_subset.mp hnv

  have hav : a ∈ v := by
    rcases hsub haW with h | h
    · exact absurd h hau
    · exact h
  have hbu : b ∈ u := by
    rcases hsub hbW with h | h
    · exact h
    · exact absurd h hbv
  have hDsub' : ball c r \ {c} ⊆ u ∪ v := hDsub.trans hsub
  have hDempty : (ball c r \ {c}) ∩ (u ∩ v) = ∅ := by
    apply Set.eq_empty_of_subset_empty
    rw [← hempty]
    exact inter_subset_inter_left _ hDsub
  rcases (isPreconnected_iff_subset_of_disjoint.mp hD) u v hu hv hDsub' hDempty with hDu | hDv
  · exact key u v hu hv hsub hempty ⟨a, haW, hav⟩ hDu
  · refine key v u hv hu ?_ ?_ ⟨b, hbW, hbu⟩ hDv
    · rwa [union_comm]
    · rwa [inter_comm u v] at hempty

theorem isPreconnected_re_gt (r : ℝ) : IsPreconnected {w : ℂ | r < w.re} := by
  have h := convex_halfSpace_gt Complex.reLm.isLinear r
  simp only [Complex.reLm_coe] at h
  exact h.isPreconnected

theorem eqOn_axis_of_eqOn_halfPlane {V U : Set ℂ} (hVo : IsOpen V) (hV : IsPreconnected V)
    (hL : ∀ s : ℂ, s.re = 0 → s ∈ V) (hH : ∀ s : ℂ, 1 / 2 < s.re → s ∈ V)
    (hUo : IsOpen U) {c : ℂ} (hc : c.re = 1 / 2) (hU : ∀ s : ℂ, 0 ≤ s.re → s ≠ c → s ∈ U)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f V) (hg : AnalyticOnNhd ℂ g U)
    (hfg : ∀ s : ℂ, 1 / 2 < s.re → f s = g s) :
    ∀ s : ℂ, s.re = 0 → f s = g s := by

  set W : Set ℂ := V \ {c} with hWdef
  have hWo : IsOpen W := hVo.sdiff isClosed_singleton
  have hW : IsPreconnected W := isPreconnected_diff_singleton hVo hV c
  have hWVU : ∀ x ∈ W, 0 ≤ x.re → x ∈ V ∩ U := fun x hx hre =>
    ⟨hx.1, hU x hre (fun h => hx.2 (mem_singleton_iff.mpr h))⟩
  set Q : Set ℂ := W ∩ {w : ℂ | 0 < w.re} with hQdef
  have hQo : IsOpen Q := hWo.inter (isOpen_lt continuous_const Complex.continuous_re)
  have h1V : (1 : ℂ) ∈ V := hH 1 (by norm_num)
  have h1c : (1 : ℂ) ≠ c := by
    intro h; rw [← h, Complex.one_re] at hc; norm_num at hc
  have h1Q : (1 : ℂ) ∈ Q := ⟨⟨h1V, fun h => h1c (mem_singleton_iff.mp h)⟩, by simp⟩
  set QH : Set ℂ := connectedComponentIn Q 1 with hQHdef
  have hQHo : IsOpen QH := hQo.connectedComponentIn
  have hQHc : IsPreconnected QH := isPreconnected_connectedComponentIn
  have hQHQ : QH ⊆ Q := connectedComponentIn_subset _ _
  have hHQ : {w : ℂ | 1 / 2 < w.re} ⊆ Q := by
    intro w hw
    have hw' : (1 : ℝ) / 2 < w.re := hw
    refine ⟨⟨hH w hw', fun h => ?_⟩, ?_⟩
    · rw [mem_singleton_iff] at h
      rw [h, hc] at hw'
      exact lt_irrefl _ hw'
    · show 0 < w.re
      linarith
  have hHQH : {w : ℂ | 1 / 2 < w.re} ⊆ QH :=
    (isPreconnected_re_gt (1 / 2)).subset_connectedComponentIn (by norm_num : (1 : ℂ) ∈ {w : ℂ | 1 / 2 < w.re}) hHQ

  have hmeet : ∃ p ∈ W, p.re = 0 ∧ p ∈ closure QH := by
    by_contra hcon
    push Not at hcon
    have h0W : (0 : ℂ) ∈ W := by
      refine ⟨hL 0 (by simp), fun h => ?_⟩
      rw [mem_singleton_iff] at h
      rw [← h, Complex.zero_re] at hc
      norm_num at hc
    have hcover : W ⊆ QH ∪ (closure QH)ᶜ := by
      intro x hx
      by_cases hxQH : x ∈ QH
      · exact Or.inl hxQH
      right
      rcases lt_trichotomy x.re 0 with hlt | heq | hgt
      ·
        intro hxcl
        rw [_root_.mem_closure_iff] at hxcl
        obtain ⟨y, hy, hyQH⟩ := hxcl {w : ℂ | w.re < 0} (isOpen_lt Complex.continuous_re continuous_const) hlt
        have : 0 < y.re := (hQHQ hyQH).2
        exact absurd hy (not_lt.mpr this.le)
      · exact hcon x hx heq
      ·
        have hxQ : x ∈ Q := ⟨hx, hgt⟩
        intro hxcl
        rw [_root_.mem_closure_iff] at hxcl
        obtain ⟨y, hy, hyQH⟩ := hxcl (connectedComponentIn Q x) hQo.connectedComponentIn
          (mem_connectedComponentIn hxQ)
        have h1 : connectedComponentIn Q x = connectedComponentIn Q y := connectedComponentIn_eq hy
        have h2 : connectedComponentIn Q 1 = connectedComponentIn Q y := connectedComponentIn_eq hyQH
        apply hxQH
        show x ∈ connectedComponentIn Q 1
        rw [h2, ← h1]
        exact mem_connectedComponentIn hxQ
    obtain ⟨x, -, hx1, hx2⟩ := hW _ _ hQHo isClosed_closure.isOpen_compl hcover ⟨1, h1Q.1, mem_connectedComponentIn h1Q⟩
      ⟨0, h0W, hcon 0 h0W (by simp)⟩
    exact hx2 (subset_closure hx1)
  obtain ⟨p, hpW, hpre, hpcl⟩ := hmeet
  have hpVU : p ∈ V ∩ U := hWVU p hpW hpre.ge
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hVo.inter hUo) p hpVU

  obtain ⟨q, hqball, hqQH⟩ : (ball p ε ∩ QH).Nonempty := by
    rw [_root_.mem_closure_iff] at hpcl
    exact hpcl _ isOpen_ball (mem_ball_self hε)
  set T : Set ℂ := QH ∪ ball p ε with hTdef
  have hTo : IsOpen T := hQHo.union isOpen_ball
  have hTc : IsPreconnected T := IsPreconnected.union q hqQH hqball hQHc (convex_ball p ε).isPreconnected
  have hTVU : T ⊆ V ∩ U := by
    rintro x (hx | hx)
    · have hxQ := hQHQ hx
      exact hWVU x hxQ.1 (le_of_lt hxQ.2)
    · exact hball hx
  have hfT : AnalyticOnNhd ℂ f T := hf.mono (fun x hx => (hTVU hx).1)
  have hgT : AnalyticOnNhd ℂ g T := hg.mono (fun x hx => (hTVU hx).2)
  have hHo : IsOpen {w : ℂ | 1 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev1 : f =ᶠ[𝓝 (1 : ℂ)] g :=
    Filter.eventuallyEq_of_mem (hHo.mem_nhds (by norm_num : (1 : ℂ) ∈ {w : ℂ | 1 / 2 < w.re}))
      (fun s hs => hfg s hs)
  have hEqT : EqOn f g T := hfT.eqOn_of_preconnected_of_eventuallyEq hgT hTc (Or.inl (hHQH (by norm_num))) hev1
  have hpT : p ∈ T := Or.inr (mem_ball_self hε)
  have hevp : f =ᶠ[𝓝 p] g := Filter.eventuallyEq_of_mem (hTo.mem_nhds hpT) hEqT

  intro s hs
  set T' : Set ℂ := connectedComponentIn (V ∩ U) p with hT'def
  have hT'o : IsOpen T' := (hVo.inter hUo).connectedComponentIn
  have hT'c : IsPreconnected T' := isPreconnected_connectedComponentIn
  have hT'VU : T' ⊆ V ∩ U := connectedComponentIn_subset _ _
  have hLimg : IsPreconnected ((fun y : ℝ => ((y : ℂ) * Complex.I)) '' univ) :=
    isPreconnected_univ.image _ (by fun_prop : Continuous fun y : ℝ => ((y : ℂ) * Complex.I)).continuousOn
  have hmemL : ∀ z : ℂ, z.re = 0 → z ∈ (fun y : ℝ => ((y : ℂ) * Complex.I)) '' univ := by
    intro z hz
    refine ⟨z.im, mem_univ _, ?_⟩
    apply Complex.ext <;> simp [hz]
  have hLVU : (fun y : ℝ => ((y : ℂ) * Complex.I)) '' univ ⊆ V ∩ U := by
    rintro z ⟨y, -, rfl⟩
    have hre : ((y : ℂ) * Complex.I).re = 0 := by simp
    refine ⟨hL _ hre, hU _ hre.ge (fun h => ?_)⟩
    have h' : ((y : ℂ) * Complex.I) = c := h
    rw [h'] at hre
    rw [hre] at hc
    norm_num at hc
  have hsT' : s ∈ T' := (hLimg.subset_connectedComponentIn (hmemL p hpre) hLVU) (hmemL s hs)
  exact (hf.mono (fun x hx => (hT'VU hx).1)).eqOn_of_preconnected_of_eventuallyEq
    (hg.mono (fun x hx => (hT'VU hx).2)) hT'c (mem_connectedComponentIn hpVU) hevp hsT'

end Topology

section KPair

variable (F : Type) [Field F] [NumberField F]

open AutomorphicForm

theorem analyticOnNhd_integral_maximalCompact {U : Set ℂ} (hU : IsOpen U)
    (Φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hΦc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Φ p.1 p.2) (U ×ˢ Set.univ))
    (hΦd : ∀ g : AdelicGL2 (𝓞 F) F, DifferentiableOn ℂ (fun s => Φ s g) U) :
    AnalyticOnNhd ℂ (fun s => ∫ k, Φ s (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) U := by
  have h := Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
    (Y := ↥(adelicMaximalCompact F)) (maximalCompactHaar F) hU (S := Set.univ) isCompact_univ
    (fun s k => Φ s (k : AdelicGL2 (𝓞 F) F)) ?_ (fun _ _ k hk => absurd (Set.mem_univ k) hk)
    (fun k => hΦd (k : AdelicGL2 (𝓞 F) F))
  · exact h.analyticOnNhd hU
  · have hcont : Continuous (fun p : ℂ × ↥(adelicMaximalCompact F) => (p.1, (p.2 : AdelicGL2 (𝓞 F) F))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    refine hΦc.comp hcont.continuousOn ?_
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩

theorem continuous_section {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)) (s : ℂ) : Continuous (φ s) :=
  hφ.comp (continuous_const.prodMk continuous_id)

theorem differentiableAt_conj_comp_conj {h : ℂ → ℂ} {s : ℂ} (hh : DifferentiableAt ℂ h (conj s)) :
    DifferentiableAt ℂ (fun w => conj (h (conj w))) s :=
  (differentiableAt_conj_conj_iff (f := h)).mpr hh

end KPair

end R4AdjAxis

open R4AdjAxis AutomorphicForm

set_option maxHeartbeats 6400000 in
theorem solution
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (_hN : N ≠ ⊥) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, φf s (g * u) = φf s g)
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst ν αm hαm s) (etaSnd μ αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite F (ψf s))
      (_hψff : ∀ s, IsKfSmooth F (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, ψf s (g * u) = ψf s g)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eψ s g = ψf s g + ∑' ξ : F, ψf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g))
      (t : ℝ),
    (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nψ (-((t : ℂ) * Complex.I)) g) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F)) =
    ∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj (ψf (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) := by
  intro αm hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu _hφflev
    ψf hψf _hψfK _hψff hψfjc hψfhol _hψfKu _hψflev Oφ Eφ Nφ hEφ Oψ Eψ Nψ hEψ t
  obtain ⟨hOφo, hOφc, hOφL, hOφH, -, hNφan, -, hNφco, -, hNφM⟩ := hEφ
  obtain ⟨hOψo, hOψc, hOψL, hOψH, -, hNψan, -, hNψco, -, hNψM⟩ := hEψ

  obtain ⟨c₁, U₁, N₁, hc₁, hU₁o, hU₁sub, hN₁an, hN₁co, hN₁M⟩ :=
    AutomorphicForm.exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family
      F hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu
  have hU₁ : ∀ s : ℂ, 0 ≤ s.re → s ≠ c₁ → s ∈ U₁ := fun s h1 h2 =>
    hU₁sub ⟨h1, fun h => h2 (Set.mem_singleton_iff.mp h)⟩

  obtain ⟨Cst, hCst⟩ : ∃ C : ℂ, C = ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ := ⟨_, rfl⟩
  have hCconj : conj Cst = Cst := by rw [hCst, map_inv₀, Complex.conj_ofReal]
  have hφc : ∀ s, Continuous (φf s) := continuous_section F hφfjc
  have hψc : ∀ s, Continuous (ψf s) := continuous_section F hψfjc

  obtain ⟨A, hA⟩ : ∃ A : ℂ → ℂ, A = fun s => ∫ k, φf s (k : AdelicGL2 (𝓞 F) F) *
      conj (Cst * Nψ (conj s) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ → ℂ, B = fun s => ∫ k, Cst * Nφ s (k : AdelicGL2 (𝓞 F) F) *
      conj (ψf (conj s) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B₁ : ℂ → ℂ, B₁ = fun s => ∫ k, Cst * N₁ s (k : AdelicGL2 (𝓞 F) F) *
      conj (ψf (conj s) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) := ⟨_, rfl⟩

  have hψ_conj_arg : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf (conj p.1) p.2 :=
    hψfjc.comp ((Complex.continuous_conj.comp continuous_fst).prodMk continuous_snd)
  have hconjψ_cont : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => conj (ψf (conj p.1) p.2) :=
    Complex.continuous_conj.comp hψ_conj_arg
  have hconjψ_diff : ∀ (g : AdelicGL2 (𝓞 F) F) (s : ℂ), DifferentiableAt ℂ (fun w => conj (ψf (conj w) g)) s :=
    fun g s => differentiableAt_conj_comp_conj ((hψfhol g).differentiableAt)
  have hBan : AnalyticOnNhd ℂ B Oφ := by
    rw [hB]
    refine analyticOnNhd_integral_maximalCompact F hOφo
      (fun s g => Cst * Nφ s g * conj (ψf (conj s) g)) ?_ ?_
    · exact (continuousOn_const.mul hNφco).mul hconjψ_cont.continuousOn
    · intro g
      exact ((differentiableOn_const _).mul (hNφan g).differentiableOn).mul
        (fun s _ => (hconjψ_diff g s).differentiableWithinAt)
  have hB₁an : AnalyticOnNhd ℂ B₁ U₁ := by
    rw [hB₁]
    refine analyticOnNhd_integral_maximalCompact F hU₁o
      (fun s g => Cst * N₁ s g * conj (ψf (conj s) g)) ?_ ?_
    · exact (continuousOn_const.mul hN₁co).mul hconjψ_cont.continuousOn
    · intro g
      exact ((differentiableOn_const _).mul (hN₁an g).differentiableOn).mul
        (fun s _ => (hconjψ_diff g s).differentiableWithinAt)
  obtain ⟨UA, hUAdef⟩ : ∃ UA : Set ℂ, UA = {s : ℂ | conj s ∈ Oψ} := ⟨_, rfl⟩
  have hmemUA : ∀ s : ℂ, s ∈ UA ↔ conj s ∈ Oψ := fun s => by rw [hUAdef]; rfl
  have hUAo : IsOpen UA := by rw [hUAdef]; exact hOψo.preimage Complex.continuous_conj
  have hUAeq : UA = (starRingEnd ℂ) '' Oψ := by
    ext z
    rw [hmemUA]
    constructor
    · intro hz
      exact ⟨conj z, hz, Complex.conj_conj z⟩
    · rintro ⟨w, hw, rfl⟩
      rwa [Complex.conj_conj]
  have hUAc : IsPreconnected UA := by
    rw [hUAeq]
    exact hOψc.image _ Complex.continuous_conj.continuousOn
  have hNψ_conj_cont : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nψ (conj p.1) p.2) (UA ×ˢ Set.univ) := by
    refine hNψco.comp ((Complex.continuous_conj.comp continuous_fst).prodMk continuous_snd).continuousOn ?_
    intro p hp
    exact ⟨(hmemUA p.1).mp hp.1, Set.mem_univ _⟩
  have hAan : AnalyticOnNhd ℂ A UA := by
    rw [hA]
    refine analyticOnNhd_integral_maximalCompact F hUAo
      (fun s g => φf s g * conj (Cst * Nψ (conj s) g)) ?_ ?_
    · exact hφfjc.continuousOn.mul
        (Complex.continuous_conj.comp_continuousOn (continuousOn_const.mul hNψ_conj_cont))
    · intro g s hs
      have hs' : conj s ∈ Oψ := (hmemUA s).mp hs
      have h1 : DifferentiableAt ℂ (fun w => Cst * Nψ w g) (conj s) :=
        (differentiableAt_const _).mul ((hNψan g (conj s) hs').differentiableAt)
      exact (((hφfhol g).differentiableAt).mul (differentiableAt_conj_comp_conj h1)).differentiableWithinAt

  have hBB₁ : ∀ s : ℂ, 1 / 2 < s.re → B s = B₁ s := by
    intro s hs
    rw [hB, hB₁]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only []
    rw [hNφM s hs, hN₁M s hs]
  have hAB₁ : ∀ s : ℂ, 1 / 2 < s.re → A s = B₁ s := by
    intro s hs
    have hs' : 1 / 2 < (conj s).re := by rwa [Complex.conj_re]
    have hW :=
      AutomorphicForm.integral_mul_conj_weylIntertwiningIntegral_eq_integral_weylIntertwiningIntegral_mul_conj_of_re_gt_half
        F hαm μ ν hμ hν s hs (φf s) (hφf s) (hφc s) (ψf (conj s)) (hψf (conj s)) (hψc (conj s))
    rw [hA, hB₁]
    simp only []
    calc (∫ k, φf s (k : AdelicGL2 (𝓞 F) F) * conj (Cst * Nψ (conj s) (k : AdelicGL2 (𝓞 F) F))
            ∂(AutomorphicForm.maximalCompactHaar F))
        = ∫ k, Cst * (φf s (k : AdelicGL2 (𝓞 F) F) *
            conj (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf (conj s))
              (k : AdelicGL2 (𝓞 F) F))) ∂(AutomorphicForm.maximalCompactHaar F) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only []
          rw [hNψM (conj s) hs', map_mul, hCconj]
          ring
      _ = Cst * ∫ k, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) (k : AdelicGL2 (𝓞 F) F) *
            conj (ψf (conj s) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) := by
          rw [integral_const_mul, hW]
      _ = ∫ k, Cst * N₁ s (k : AdelicGL2 (𝓞 F) F) * conj (ψf (conj s) (k : AdelicGL2 (𝓞 F) F))
            ∂(AutomorphicForm.maximalCompactHaar F) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only []
          rw [hN₁M s hs, mul_assoc]

  have hgB : ∀ s : ℂ, s.re = 0 → B s = B₁ s :=
    eqOn_axis_of_eqOn_halfPlane hOφo hOφc (fun s hs => hOφL hs) (fun s hs => hOφH hs) hU₁o hc₁ hU₁
      hBan hB₁an hBB₁
  have hLUA : ∀ s : ℂ, s.re = 0 → s ∈ UA := fun s hs =>
    (hmemUA s).mpr (hOψL (show (conj s).re = 0 by rw [Complex.conj_re, hs]))
  have hHUA : ∀ s : ℂ, 1 / 2 < s.re → s ∈ UA := fun s hs =>
    (hmemUA s).mpr (hOψH (show 1 / 2 < (conj s).re by rwa [Complex.conj_re]))
  have hgA : ∀ s : ℂ, s.re = 0 → A s = B₁ s :=
    eqOn_axis_of_eqOn_halfPlane hUAo hUAc hLUA hHUA hU₁o hc₁ hU₁ hAan hB₁an hAB₁

  have hs₀ : ((t : ℂ) * Complex.I).re = 0 := by simp
  have hconj : conj ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have key : A ((t : ℂ) * Complex.I) = B ((t : ℂ) * Complex.I) :=
    (hgA _ hs₀).trans (hgB _ hs₀).symm
  rw [hA, hB] at key
  simp only [hconj] at key
  subst hCst
  simp only []
  exact key

end
end S_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
end P2MW
export P2MW.S_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot (solution)
