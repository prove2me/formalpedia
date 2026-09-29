-- Prove2me | solution 1 for AutomorphicForm.peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/924c766e-0b6e-59cf-8503-e8d34d3a8dac

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace PetNe17

open scoped Pointwise ENNReal

section FDAction

variable {H α : Type*} [Group H] [MulAction H α] [MeasurableSpace α] [MeasurableConstSMul H α]
  [Countable H] {ν : Measure α} [SMulInvariantMeasure H α ν]

theorem exists_measure_smul_inter_ne_zero {S U : Set α} (hS : IsFundamentalDomain H S ν)
    (hU : ν U ≠ 0) : ∃ γ : H, ν (γ • U ∩ S) ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hU ((hS.measure_eq_tsum U).trans (ENNReal.tsum_eq_zero.mpr h))

end FDAction

section Group

variable {G : Type*} [Group G] [MeasurableSpace G]

theorem smulInvariantMeasure_restrict (Γ : Subgroup G) [MeasurableConstSMul ↥Γ G]
    (μ : Measure G) [SMulInvariantMeasure ↥Γ G μ] {T : Set G} (hT : MeasurableSet T)
    (hΓT : ∀ γ : ↥Γ, (fun w : G => γ • w) ⁻¹' T = T) :
    SMulInvariantMeasure ↥Γ G (μ.restrict T) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply (hA.preimage (measurable_const_smul _)), Measure.restrict_apply hA]
  conv_lhs => rw [← hΓT γ, ← Set.preimage_inter]
  exact SMulInvariantMeasure.measure_preimage_smul γ (hA.inter hT)

end Group

section Positivity

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [BorelSpace G]

theorem setIntegral_pos_of_isFundamentalDomain (Γ : Subgroup G) [Countable ↥Γ]
    [MeasurableConstSMul ↥Γ G] (μ : Measure G) [μ.IsOpenPosMeasure] {S T : Set G}
    [SMulInvariantMeasure ↥Γ G (μ.restrict T)]
    (hS : IsFundamentalDomain ↥Γ S (μ.restrict T)) (F : G → ℝ)
    (hF0 : ∀ w, 0 ≤ F w) (hFΓ : ∀ (γ : ↥Γ) (w : G), F (γ • w) = F w)
    (hint : IntegrableOn F S μ) {U : Set G} (hUo : IsOpen U) (hUne : U.Nonempty) (hUT : U ⊆ T)
    (hUF : ∀ w ∈ U, 0 < F w) : 0 < ∫ w in S, F w ∂μ := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun w => hF0 w) hint]
  have hU : (μ.restrict T) U ≠ 0 := by
    rw [Measure.restrict_apply hUo.measurableSet, Set.inter_eq_self_of_subset_left hUT]
    exact (hUo.measure_pos μ hUne).ne'
  obtain ⟨γ, hγ⟩ := exists_measure_smul_inter_ne_zero hS hU
  have hsub : γ • U ∩ S ⊆ Function.support F ∩ S := by
    rintro w ⟨⟨u, hu, rfl⟩, hw⟩
    exact ⟨show F (γ • u) ≠ 0 by rw [hFΓ γ u]; exact (hUF u hu).ne', hw⟩
  refine pos_iff_ne_zero.mpr fun h0 => hγ (nonpos_iff_eq_zero.mp ?_)
  calc (μ.restrict T) (γ • U ∩ S) ≤ μ (γ • U ∩ S) := Measure.le_iff'.mp Measure.restrict_le_self _
    _ ≤ μ (Function.support F ∩ S) := measure_mono hsub
    _ = 0 := h0

end Positivity

section Adelic

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

abbrev dn (g : AdelicGL2 (𝓞 F) F) : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det g)

abbrev slab (F : Type) [Field F] [NumberField F] (a b : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

abbrev Γp (F : Type) [Field F] [NumberField F] : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (globalPoints (𝓞 F) F).range

scoped instance instCountableF : Countable F :=
  (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

scoped instance instCountableΓ : Countable ↥(Γp F) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (GL (Fin 2) F) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 F) F)).countable

theorem dn_pos (g : AdelicGL2 (𝓞 F) F) : 0 < dn g := ideleNorm_pos _

theorem dn_mul (g h : AdelicGL2 (𝓞 F) F) : dn (g * h) = dn g * dn h := by
  show ideleNorm F _ = _
  rw [map_mul, ideleNorm_mul]

theorem dn_globalPoints_mul (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    dn (globalPoints (𝓞 F) F γ * g) = dn g := by
  rw [dn_mul]
  show ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ)) * dn g = dn g
  rw [AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem dn_subtype_mul (γ : ↥(Γp F)) (g : AdelicGL2 (𝓞 F) F) : dn ((γ : AdelicGL2 (𝓞 F) F) * g) = dn g := by
  obtain ⟨_, γ', rfl⟩ := γ
  exact dn_globalPoints_mul γ' g

theorem continuous_dn : Continuous (fun g : AdelicGL2 (𝓞 F) F => dn g) :=
  NumberField.TateGlobal.continuous_ideleNorm_det F

theorem measurableSet_slab (a b : ℝ) : MeasurableSet (slab F a b) :=
  (isClosed_Icc.preimage continuous_dn).measurableSet

theorem preimage_subtype_mul_slab (γ : ↥(Γp F)) (a b : ℝ) :
    (fun w : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * w) ⁻¹' slab F a b = slab F a b := by
  ext w
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [show ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * w)) = dn w from
    dn_subtype_mul γ w]

theorem smulInvariantMeasure_slab (a b : ℝ) :
    SMulInvariantMeasure ↥(Γp F) (AdelicGL2 (𝓞 F) F) ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F a b)) :=
  smulInvariantMeasure_restrict (Γp F) (adelicGLHaar (Fin 2) (𝓞 F) F) (measurableSet_slab a b)
    (fun γ => preimage_subtype_mul_slab γ a b)

theorem peterssonIntegral_self (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F s S f f = ((∫ w in S, ‖f w‖ ^ 2 * dn w ^ (-s) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ) := by
  show (∫ w in S, f w * (starRingEnd ℂ) (f w) * ((dn w ^ (-s) : ℝ) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) = _
  have h : ∀ w, f w * (starRingEnd ℂ) (f w) * ((dn w ^ (-s) : ℝ) : ℂ) = ((‖f w‖ ^ 2 * dn w ^ (-s) : ℝ) : ℂ) :=
    fun w => by
      rw [Complex.mul_conj, Complex.ofReal_mul, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp_rw [h]
  exact integral_ofReal

theorem setIntegral_norm_sq_wt_pos {S : Set (AdelicGL2 (𝓞 F) F)} {α β : ℝ}
    (hS : IsFundamentalDomain ↥(Γp F) S ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F α β))) (s : ℝ)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : Continuous f)
    (hΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (hne : ∃ g, dn g ∈ Set.Ioo α β ∧ f g ≠ 0)
    (hint : IntegrableOn (fun w => ‖f w‖ ^ 2 * dn w ^ (-s)) S (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    0 < ∫ w in S, ‖f w‖ ^ 2 * dn w ^ (-s) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := smulInvariantMeasure_slab (F := F) α β
  obtain ⟨g₀, hg₀, hfg₀⟩ := hne
  refine setIntegral_pos_of_isFundamentalDomain (Γp F) (adelicGLHaar (Fin 2) (𝓞 F) F) (T := slab F α β) hS
    (fun w => ‖f w‖ ^ 2 * dn w ^ (-s)) (fun w => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (dn_pos w).le _))
    ?_ hint (U := {g | dn g ∈ Set.Ioo α β} ∩ {g | f g ≠ 0}) ?_ ?_ ?_ ?_
  · rintro ⟨_, γ, rfl⟩ w
    show ‖f (globalPoints (𝓞 F) F γ * w)‖ ^ 2 * dn (globalPoints (𝓞 F) F γ * w) ^ (-s) = _
    rw [hΓ, dn_globalPoints_mul]
  · exact (isOpen_Ioo.preimage continuous_dn).inter (isOpen_compl_singleton.preimage hf)
  · exact ⟨g₀, hg₀, hfg₀⟩
  · exact fun g hg => Set.Ioo_subset_Icc_self hg.1
  · exact fun w hw => mul_pos (pow_pos (norm_pos_iff.mpr hw.2) 2) (Real.rpow_pos_of_pos (dn_pos w) _)

end Adelic

end PetNe17
p2m_reactivate "P2MW.S_AutomorphicForm_peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous.PetNe17"

end
p2m_reactivate "P2MW.S_AutomorphicForm_peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous.PetNe17"

open PetNe17 in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (w e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      x (globalPoints (𝓞 K) K γ * g) = x g)
    (hne : ∃ g : AdelicGL2 (𝓞 K) K,
      ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo e₁ e₂ ∧ x g ≠ 0)
    (hint : IntegrableOn (fun g => ‖x g‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕
      (adelicGLHaar (Fin 2) (𝓞 K) K)) :
    peterssonIntegral K w 𝓕 x x ≠ 0 := by
  rw [peterssonIntegral_self, Complex.ofReal_ne_zero]
  exact (setIntegral_norm_sq_wt_pos (F := K) h𝓕 w hxc hxG hne hint).ne'

end S_AutomorphicForm_peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
end P2MW
export P2MW.S_AutomorphicForm_peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous (solution)
