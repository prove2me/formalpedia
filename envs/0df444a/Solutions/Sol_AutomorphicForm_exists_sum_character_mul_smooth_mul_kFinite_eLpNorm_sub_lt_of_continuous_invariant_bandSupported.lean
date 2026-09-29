-- Prove2me | solution 1 for AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_continuous_invariant_bandSupported
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ff264c61-c8fd-5a37-9c59-ea627c7696f4

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm
import Theorems.Thm_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported
import Theorems.Thm_NumberField_Idele_withDensity_inv_ideleNorm_restrict_prod_maximalCompactHaar_band_lt_top
import Theorems.Thm_NumberField_Idele_aestronglyMeasurable_of_continuous_prod_maximalCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_continuous_invariant_bandSupported
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem solution
    (F : Type) [Field F] [NumberField F]
    (a' b' a₁ b₁ : ℝ) (ha' : 0 < a') (ha₁ : a' < a₁) (hb₁ : b₁ < b')
    (G : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ) (hGc : Continuous G)
    (hGinv : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G (γ * p.1, p.2) = G p)
    (hGsupp : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G p ≠ 0 → NumberField.TateGlobal.ideleNorm F p.1 ∈ Set.Icc a₁ b₁)
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (μ : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (h : Fin n → ℝ → ℂ)
      (m : Fin n → ↥(adelicMaximalCompact F) → ℂ),
      (∀ j, IsUnitaryChar (𝓞 F) F (μ j)) ∧ (∀ j, IsIdeleClassChar (𝓞 F) F (μ j)) ∧
      (∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ j x : ℂˣ) : ℂ)) ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (h j)) ∧ (∀ j, HasCompactSupport (h j)) ∧
      (∀ (j : Fin n) (u : ℝ), h j u ≠ 0 → u ∈ Set.Icc (Real.log a') (Real.log b')) ∧
      (∀ j, Continuous (m j)) ∧
      (∀ j, ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
        ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => m j (k * k₀)) ∈ W) ∧
      (∀ j, ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u : ↥(adelicMaximalCompact F)),
        (u : AdelicGL2 (𝓞 F) F) ∈ V → (u : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F →
          m j (k * u) = m j k) ∧
      AEStronglyMeasurable (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => G p - ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2)
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) ∧
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => G p - ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) < ENNReal.ofReal δ := by
  classical
  have hnorm_cont : Continuous (NumberField.TateGlobal.ideleNorm F) := NumberField.TateGlobal.continuous_ideleNorm F

  by_cases hb' : b' ≤ 0
  · have hG0 : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G p = 0 := by
      intro p
      by_contra hne
      have h1 := hGsupp p hne
      have : (0 : ℝ) < b₁ := lt_of_lt_of_le (lt_of_lt_of_le ha' (le_trans ha₁.le h1.1)) h1.2
      linarith
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
      fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
      ?_, ?_⟩
    · have hGz : G = fun _ => 0 := funext hG0
      simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, hGz]
      exact aestronglyMeasurable_const
    · have hGz : G = fun _ => 0 := funext hG0
      simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, hGz, eLpNorm_zero']
      exact ENNReal.ofReal_pos.mpr hδ
  push Not at hb'

  set B : Set ((AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F)) := {p | NumberField.TateGlobal.ideleNorm F p.1 ∈ Set.Icc a' b'} with hB
  have hBmeas : MeasurableSet B :=
    (hnorm_cont.measurable.comp measurable_fst) measurableSet_Icc
  have hBfin := NumberField.Idele.withDensity_inv_ideleNorm_restrict_prod_maximalCompactHaar_band_lt_top F D hDm hDF a' b' ha'
  set M : ℝ≥0∞ := ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) B with hM
  have hMtop : M < ⊤ := hBfin

  obtain ⟨ε, hε, hεM⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε * M ^ ((1 : ℝ) / 2) < ENNReal.ofReal δ := by
    have hM2 : M ^ ((1 : ℝ) / 2) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hMtop.ne
    set r : ℝ := (M ^ ((1 : ℝ) / 2)).toReal with hr
    have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
    refine ⟨δ / (2 * (r + 1)), by positivity, ?_⟩
    rw [← ENNReal.ofReal_toReal hM2, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_ofReal_iff hδ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨n, μ, h, m, c1, c2, c3, c4, c5, c6, c7, c8, c9, hunif⟩ :=
    AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported
      F a' b' a₁ b₁ ha' ha₁ hb₁ G hGc hGinv hGsupp ε hε

  have hEc : Continuous fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2 := by
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => ((μ j p.1 : ℂˣ) : ℂ) := (c3 j).comp continuous_fst
    have h2 : Continuous fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) := by
      refine (c4 j).continuous.comp ?_
      exact Real.continuousOn_log.comp_continuous (hnorm_cont.comp continuous_fst)
        (fun p => (NumberField.TateGlobal.ideleNorm_pos (p.1)).ne')
    have h3 : Continuous fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => m j p.2 := (c7 j).comp continuous_snd
    exact (h1.mul h2).mul h3
  refine ⟨n, μ, h, m, c1, c2, c3, c4, c5, c6, c7, c8, c9, ?_, ?_⟩
  · exact NumberField.Idele.aestronglyMeasurable_of_continuous_prod_maximalCompact F D hDm _ (hGc.sub hEc)
  ·
    have hptw : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), ‖G p - ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2‖ ≤
        ‖B.indicator (fun _ => (ε : ℂ)) p‖ := by
      intro p
      by_cases hp : p ∈ B
      · rw [Set.indicator_of_mem hp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
        exact hunif p
      · have hG : G p = 0 := by
          by_contra hne
          exact hp ⟨le_trans ha₁.le (hGsupp p hne).1, le_trans (hGsupp p hne).2 hb₁.le⟩
        have hS : (∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          have hz : h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) = 0 := by
            by_contra hne
            have hu := c6 j _ hne
            have hpos := NumberField.TateGlobal.ideleNorm_pos (F := F) p.1
            exact hp ⟨(Real.log_le_log_iff ha' hpos).mp hu.1, (Real.log_le_log_iff hpos hb').mp hu.2⟩
          rw [hz, mul_zero, zero_mul]
        rw [hG, hS, Set.indicator_of_notMem hp]
        simp
    calc eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => G p - ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2) 2 _
        ≤ eLpNorm (B.indicator fun _ => (ε : ℂ)) 2 _ := eLpNorm_mono (fun p => hptw p)
      _ = ‖(ε : ℂ)‖ₑ * M ^ ((1 : ℝ) / 2) := by
          rw [eLpNorm_indicator_const hBmeas (by norm_num) (by norm_num)]
          norm_num
          rfl
      _ < ENNReal.ofReal δ := by
          rw [show ‖(ε : ℂ)‖ₑ = ENNReal.ofReal ε by
            rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]]
          exact hεM

end

end S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_continuous_invariant_bandSupported
end P2MW
export P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_continuous_invariant_bandSupported (solution)
