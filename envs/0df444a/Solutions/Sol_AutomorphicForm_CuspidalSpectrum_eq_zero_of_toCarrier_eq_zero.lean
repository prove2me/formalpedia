-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d33f09c2-4ae1-54a2-a658-c0195fbcf565

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ contMemberSubmodule F Φ₀ ξ)
    (h0 : toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩ = 0) : φ = 0 := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  have hcont : Continuous φ := hφ.2
  obtain ⟨⟨hleft, hcentral⟩, -⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1
  have hdetcont := NumberField.TateGlobal.continuous_ideleNorm_det F

  have h1 : ∀ᵐ x ∂(μ.restrict Φ₀), φ x = 0 := by
    have hw : φ =ᵐ[weightedMeasure F Φ₀ σ] 0 := by
      have h0' : (memLp_weightedMeasure_of_mem F hΦ₀ σ hφ.1).toLp φ = 0 := h0
      have h := (memLp_weightedMeasure_of_mem F hΦ₀ σ hφ.1).coeFn_toLp
      rw [h0'] at h
      exact h.symm.trans (Lp.coeFn_zero _ _ _)
    have hmeas : Measurable fun x : AdelicGL2 (𝓞 F) F => ENNReal.ofReal (weight F σ x) := by
      refine Measurable.ennreal_ofReal ?_
      show Measurable fun x : AdelicGL2 (𝓞 F) F =>
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ)
      exact hdetcont.measurable.pow_const _
    rw [weightedMeasure_def, Filter.EventuallyEq, ae_withDensity_iff hmeas] at hw
    filter_upwards [hw] with x hx
    refine hx ?_
    have hpos : 0 < weight F σ x := Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _
    exact (ENNReal.ofReal_pos.mpr hpos).ne'

  set S : Set (AdelicGL2 (𝓞 F) F) := detNormSlab F α β with hS
  set B : Set (AdelicGL2 (𝓞 F) F) := {x | φ x ≠ 0} ∩ Φ₀ with hB
  have hBnull : μ B = 0 := by
    have h := ae_iff.mp h1
    rw [Measure.restrict_apply (isOpen_ne_fun hcont continuous_const).measurableSet] at h
    exact h
  set Γ : Subgroup (AdelicGL2 (𝓞 F) F) := (globalPoints (𝓞 F) F).range with hΓ
  haveI : Countable F := by
    exact (Module.finBasis ℚ F).equivFun.injective.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable (f := (Units.val : Matrix.GeneralLinearGroup (Fin 2) F → Matrix (Fin 2) (Fin 2) F))
      (fun a b h => Units.ext h)
  haveI : Countable Γ := (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 F) F)).countable
  have hpre : ∀ γ : Γ, μ ((fun x => (γ : AdelicGL2 (𝓞 F) F) * x) ⁻¹' B) = 0 := fun γ => by
    rw [measure_preimage_mul]; exact hBnull
  have hU : μ (⋃ γ : Γ, (fun x => (γ : AdelicGL2 (𝓞 F) F) * x) ⁻¹' B) = 0 := measure_iUnion_null hpre
  have h2 : ∀ᵐ x ∂(μ.restrict S), φ x = 0 := by
    have hcov : ∀ᵐ x ∂(μ.restrict S), ∃ γ : Γ, γ • x ∈ Φ₀ := hΦ₀.isFundamentalDomain.ae_covers
    have hnot : ∀ᵐ x ∂(μ.restrict S), x ∈ (⋃ γ : Γ, (fun x => (γ : AdelicGL2 (𝓞 F) F) * x) ⁻¹' B)ᶜ :=
      ae_restrict_of_ae (compl_mem_ae_iff.mpr hU)
    filter_upwards [hcov, hnot] with x hx hxn
    obtain ⟨γ, hγ⟩ := hx
    by_contra hne
    apply hxn
    refine Set.mem_iUnion.mpr ⟨γ, ?_⟩
    show (γ : AdelicGL2 (𝓞 F) F) * x ∈ B
    refine ⟨?_, ?_⟩
    · obtain ⟨γ₀, hγ₀⟩ := γ.2
      show φ ((γ : AdelicGL2 (𝓞 F) F) * x) ≠ 0
      rw [← hγ₀, hleft]
      exact hne
    · simpa [Subgroup.smul_def, smul_eq_mul] using hγ

  by_contra hφne
  obtain ⟨y, hy⟩ : ∃ y, φ y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφne (funext h)
  obtain ⟨s, -, hs, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F
  set ny : ℝ := NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) with hny
  have hny_pos : 0 < ny := NumberField.TateGlobal.ideleNorm_pos _
  set t : ℝ := (α + β) / 2 with ht
  have hαβ : α < β := hΦ₀.lt
  have hαt : α < t := by rw [ht]; linarith
  have htβ : t < β := by rw [ht]; linarith
  have ht_pos : 0 < t := hΦ₀.pos.trans hαt
  set rr : ℝ := Real.sqrt (t / ny) with hrr
  have hrr_pos : 0 < rr := Real.sqrt_pos.mpr (div_pos ht_pos hny_pos)
  set r : ℝ≥0ˣ := Units.mk0 ⟨rr, hrr_pos.le⟩ (by
    intro h
    have := congrArg (fun q : ℝ≥0 => (q : ℝ)) h
    simp only [NNReal.coe_mk, NNReal.coe_zero] at this
    exact hrr_pos.ne' this) with hr
  have hz : NumberField.TateGlobal.ideleNorm F (s r) = rr := by
    rw [hs r]
    rfl
  have key : φ (centralScalar (𝓞 F) F (s r) * y) = ((ξ ⟨s r, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * φ y :=
    hcentral ⟨s r, Subgroup.mem_top _⟩ y
  have hφx : φ (centralScalar (𝓞 F) F (s r) * y) ≠ 0 := by
    rw [key]
    exact mul_ne_zero (Units.ne_zero _) hy
  have hdet : Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (s r)) = s r * s r := by
    show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) (s r)) = s r * s r
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_two]
  have hdetx : NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (s r) * y)) = t := by
    rw [map_mul, hdet, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul, hz, ← hny]
    have hsq : rr * rr = t / ny := Real.mul_self_sqrt (div_pos ht_pos hny_pos).le
    rw [hsq, div_mul_cancel₀ _ hny_pos.ne']
  have hopen : IsOpen {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β} :=
    isOpen_Ioo.preimage hdetcont
  have hsub : {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β} ⊆ S :=
    fun g hg => (mem_detNormSlab F α β g).mpr ⟨hg.1.le, hg.2.le⟩
  have hxint : centralScalar (𝓞 F) F (s r) * y ∈ interior S :=
    interior_maximal hsub hopen (show _ ∈ Set.Ioo α β by rw [hdetx]; exact ⟨hαt, htβ⟩)
  exact not_ae_zero_restrict_of_continuous_of_mem_interior (μ := μ) hcont hφx hxint h2

end S_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero (solution)
