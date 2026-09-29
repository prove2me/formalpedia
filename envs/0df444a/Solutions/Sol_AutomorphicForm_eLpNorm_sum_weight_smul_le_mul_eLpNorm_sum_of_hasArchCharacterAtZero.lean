-- Prove2me | solution 1 for AutomorphicForm.eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5f27ba1f-5c75-5a3f-aa86-2e3c9a87a335

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain
open scoped ComplexConjugate ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace KtR

variable {K : Type} [Field K] [NumberField K]

section Slab

open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

abbrev slab (K : Type) [Field K] [NumberField K] (a b : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

abbrev Γp (K : Type) [Field K] [NumberField K] : Subgroup (AdelicGL2 (𝓞 K) K) :=
  (globalPoints (𝓞 K) K).range

scoped instance instCountableK : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

scoped instance instCountableΓ : Countable ↥(Γp K) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (GL (Fin 2) K) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 K) K)).countable

theorem measurableSet_slab (a b : ℝ) : MeasurableSet (slab K a b) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K a b

theorem preimage_subtype_mul_slab (γ : ↥(Γp K)) (a b : ℝ) :
    (fun g : AdelicGL2 (𝓞 K) K => (γ : AdelicGL2 (𝓞 K) K) * g) ⁻¹' slab K a b = slab K a b := by
  obtain ⟨_, γ', rfl⟩ := γ
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq, MonoidHom.coe_rangeRestrict, map_mul,
    NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem smulInvariantMeasure_slab (a b : ℝ) :
    SMulInvariantMeasure ↥(Γp K) (AdelicGL2 (𝓞 K) K) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply (hA.preimage (measurable_const_smul _)), Measure.restrict_apply hA]
  conv_lhs => rw [← preimage_subtype_mul_slab γ a b]
  rw [show (fun x : AdelicGL2 (𝓞 K) K => γ • x) = fun g => (γ : AdelicGL2 (𝓞 K) K) * g from rfl, ← Set.preimage_inter]
  exact SMulInvariantMeasure.measure_preimage_smul γ (hA.inter (measurableSet_slab a b))

theorem exists_measurable_fd (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ 𝓕 : Set (AdelicGL2 (𝓞 K) K), MeasurableSet 𝓕 ∧ 𝓕 ⊆ slab K α β ∧
      IsFundamentalDomain (↥(Γp K)) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)) ∧
      (adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕 =
        (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β) ∧
      adelicGLHaar (Fin 2) (𝓞 K) K 𝓕 < ⊤ := by
  obtain ⟨-, -, -, hΦs, hΦ⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  set Φ₀ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ₀
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set ν := μ.restrict (slab K α β) with hν
  haveI := smulInvariantMeasure_slab (K := K) α β
  obtain ⟨t, ht_sub, ht_m, ht_eq⟩ := hΦ.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hdiff : ν (Φ₀ \ t) = 0 := (ae_eq_set.1 ht_eq).2
  refine ⟨t, ht_m, ht_sub.trans hΦs, ?_, ?_, ?_⟩
  · refine ⟨ht_m.nullMeasurableSet, ?_, fun a b hab => (hΦ.aedisjoint hab).mono
      (Set.smul_set_mono ht_sub) (Set.smul_set_mono ht_sub)⟩
    have hnull : ∀ γ : ↥(Γp K), ∀ᵐ x ∂ν, γ • x ∉ Φ₀ \ t := by
      intro γ
      have h0 : ν ((fun x => γ • x) ⁻¹' (Φ₀ \ t)) = 0 := by
        rw [Set.preimage_smul]
        exact measure_smul_null hdiff γ⁻¹
      exact (measure_eq_zero_iff_ae_notMem.1 h0)
    have hall : ∀ᵐ x ∂ν, ∀ γ : ↥(Γp K), γ • x ∉ Φ₀ \ t := ae_all_iff.2 hnull
    filter_upwards [hΦ.ae_covers, hall] with x hx h2
    obtain ⟨γ, hγ⟩ := hx
    exact ⟨γ, by_contra fun h => h2 γ ⟨hγ, h⟩⟩
  · have h1 : μ (Φ₀ \ t) = 0 := by
      have h := hdiff
      rw [hν, Measure.restrict_apply' (measurableSet_slab α β),
        Set.inter_eq_self_of_subset_left (Set.diff_subset.trans hΦs)] at h
      exact h
    exact Measure.restrict_congr_set (ae_eq_set.2 ⟨by rw [Set.diff_eq_empty.2 ht_sub, measure_empty], h1⟩)
  · exact (measure_mono (Set.subset_inter ht_sub (ht_sub.trans hΦs))).trans_lt
      (AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ Φ₀ hΦ)

variable {w : InfinitePlace K}

abbrev incl (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) : AdelicGL2 (𝓞 K) K :=
  adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion)

theorem ideleNorm_det_incl (k : rowIsometrySubgroup₀ w.Completion) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (incl w k)) = 1 := by
  have hfin : glFin (𝓞 K) K (incl w k) ∈ finiteIntegralGL2 (𝓞 K) K := by
    have : glFin (𝓞 K) K (incl w k) = 1 := glFin_adelicArchGLIncl K _
    rw [this]
    exact Subgroup.one_mem _
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K (incl w k) hfin]
  refine Finset.prod_eq_one fun v _ => ?_
  have hglArch : glArch (𝓞 K) K (incl w k) = archGLIncl K w (k : GL (Fin 2) w.Completion) :=
    glArch_adelicArchGLIncl K _
  have h1 : NumberField.AdelicVolume.archDetNorm v (incl w k) = 1 := by
    unfold NumberField.AdelicVolume.archDetNorm
    rw [hglArch]
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_self]
      obtain ⟨hd, -⟩ := (mem_rowIsometrySubgroup₀_iff _).1 k.2
      rw [hd, norm_one]
    · rw [archComponent_archGLIncl_of_ne K hv, Units.val_one, Matrix.det_one, norm_one]
  rw [h1, one_pow]

theorem ideleNorm_det_mul_incl (k : rowIsometrySubgroup₀ w.Completion) (g : AdelicGL2 (𝓞 K) K) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (g * incl w k)) =
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_incl, mul_one]

theorem preimage_mul_incl_slab (k : rowIsometrySubgroup₀ w.Completion) (a b : ℝ) :
    (fun g : AdelicGL2 (𝓞 K) K => g * incl w k) ⁻¹' slab K a b = slab K a b := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq, ideleNorm_det_mul_incl]

theorem image_mul_incl_subset (k : rowIsometrySubgroup₀ w.Completion) {a b : ℝ} {𝓕 : Set (AdelicGL2 (𝓞 K) K)}
    (h : 𝓕 ⊆ slab K a b) : (fun g : AdelicGL2 (𝓞 K) K => g * incl w k) '' 𝓕 ⊆ slab K a b := by
  rintro _ ⟨g, hg, rfl⟩
  show NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (g * incl w k)) ∈ Set.Icc a b
  rw [ideleNorm_det_mul_incl]
  exact h hg

theorem measurePreserving_mul_right' (x : AdelicGL2 (𝓞 K) K) :
    MeasurePreserving (fun g : AdelicGL2 (𝓞 K) K => g * x)
      (adelicGLHaar (Fin 2) (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  exact measurePreserving_mul_right (adelicGLHaar (Fin 2) (𝓞 K) K) x

theorem isFundamentalDomain_image_mul_incl (k : rowIsometrySubgroup₀ w.Completion) (a b : ℝ)
    {𝓕 : Set (AdelicGL2 (𝓞 K) K)}
    (h𝓕 : IsFundamentalDomain ↥(Γp K) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b))) :
    IsFundamentalDomain ↥(Γp K) ((fun g : AdelicGL2 (𝓞 K) K => g * incl w k) '' 𝓕)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
  have hcoe : (⇑(Equiv.mulRight (incl w k)) : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K) =
      fun g => g * incl w k := Equiv.coe_mulRight _
  have hqmp : Measure.QuasiMeasurePreserving (⇑(Equiv.mulRight (incl w k)).symm)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b))
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
    rw [Equiv.mulRight_symm, Equiv.coe_mulRight]
    have hinv : (incl w k)⁻¹ = incl w k⁻¹ := by
      show (adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion))⁻¹ = adelicArchGLInclAt K w ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)
      rw [Subgroup.coe_inv, map_inv]
    rw [hinv]
    have h1 := (measurePreserving_mul_right' (K := K) (incl w k⁻¹)).restrict_preimage
      (measurableSet_slab (K := K) a b)
    rw [preimage_mul_incl_slab] at h1
    exact h1.quasiMeasurePreserving
  have h := h𝓕.image_of_equiv (Equiv.mulRight (incl w k)) hqmp (Equiv.refl _) (fun γ g => by
    show (((Equiv.refl _ γ : ↥(Γp K)) : AdelicGL2 (𝓞 K) K) * g) * incl w k =
      (γ : AdelicGL2 (𝓞 K) K) * (g * incl w k)
    rw [Equiv.refl_apply, mul_assoc])
  rwa [hcoe] at h

theorem setIntegral_comp_mul_incl_eq (k : rowIsometrySubgroup₀ w.Completion) (a b : ℝ)
    {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h𝓕s : 𝓕 ⊆ slab K a b)
    (h𝓕 : IsFundamentalDomain ↥(Γp K) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)))
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * g) = f g) :
    ∫ g in 𝓕, f (g * incl w k) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in 𝓕, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := smulInvariantMeasure_slab (K := K) a b
  have hemb : MeasurableEmbedding (fun g : AdelicGL2 (𝓞 K) K => g * incl w k) :=
    (Homeomorph.mulRight (incl w k)).measurableEmbedding
  have hsub := image_mul_incl_subset k h𝓕s
  have hinv : ∀ (γ : ↥(Γp K)) (g : AdelicGL2 (𝓞 K) K), f (γ • g) = f g := by
    rintro ⟨_, γ', rfl⟩ g
    exact hf γ' g
  calc ∫ g in 𝓕, f (g * incl w k) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ h in (fun g : AdelicGL2 (𝓞 K) K => g * incl w k) '' 𝓕, f h ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        ((measurePreserving_mul_right' (K := K) (incl w k)).setIntegral_image_emb hemb f 𝓕).symm
    _ = ∫ h in (fun g : AdelicGL2 (𝓞 K) K => g * incl w k) '' 𝓕, f h
          ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
        rw [Measure.restrict_restrict_of_subset hsub]
    _ = ∫ h in 𝓕, f h ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) :=
        (isFundamentalDomain_image_mul_incl k a b h𝓕).setIntegral_eq h𝓕 hinv
    _ = ∫ g in 𝓕, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        rw [Measure.restrict_restrict_of_subset h𝓕s]

end Slab

end KtR
p2m_reactivate "P2MW.S_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero.KtR"

namespace KtR

variable {K : Type} [Field K] [NumberField K]

section Pairing

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

theorem integrable_mul_conj {α β : ℝ} {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ slab K α β) (hfin : adelicGLHaar (Fin 2) (𝓞 K) K 𝓕 < ⊤)
    {f h : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (hh : Continuous h) {B B' : ℝ}
    (hbf : ∀ g, g ∈ slab K α β → ‖f g‖ ≤ B) (hbh : ∀ g, g ∈ slab K α β → ‖h g‖ ≤ B') :
    Integrable (fun g => f g * conj (h g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕) := by
  refine Measure.integrableOn_of_bounded (M := B * B') hfin.ne
    (hf.mul (Complex.continuous_conj.comp hh)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' h𝓕m]
  refine ae_of_all _ fun g hg => ?_
  rw [norm_mul, Complex.norm_conj]
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbf g (h𝓕s hg))
  exact mul_le_mul (hbf g (h𝓕s hg)) (hbh g (h𝓕s hg)) (norm_nonneg _) hB

theorem setIntegral_mul_conj_self (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (f : AdelicGL2 (𝓞 K) K → ℂ) :
    ∫ g in 𝓕, f g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((∫ g in 𝓕, ‖f g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext g
  rw [Complex.mul_conj', Complex.ofReal_pow]

theorem eLpNorm_two_eq_sqrt {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h𝓕m : MeasurableSet 𝓕)
    (hfin : adelicGLHaar (Fin 2) (𝓞 K) K 𝓕 < ⊤) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) {B : ℝ}
    (hb : ∀ g, g ∈ 𝓕 → ‖f g‖ ≤ B) :
    eLpNorm f 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕) =
      ENNReal.ofReal (Real.sqrt (∫ g in 𝓕, ‖f g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  have hmem : MemLp f 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕) :=
    MemLp.of_bound hf.aestronglyMeasurable B ((ae_restrict_iff' h𝓕m).2 (ae_of_all _ hb))
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, Real.sqrt_eq_rpow, one_div]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

end Pairing
p2m_reactivate "P2MW.S_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero.KtR"

section Rotation

open NumberField.InfinitePlace.Completion

def rotR (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]
    (by rw [Matrix.det_fin_two_of]; nlinarith [Real.cos_sq_add_sin_sq θ])

theorem rotR_apply (θ : ℝ) (i j : Fin 2) :
    (rotR θ : Matrix (Fin 2) (Fin 2) ℝ) i j = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] i j := rfl

theorem rotR_mem (θ : ℝ) : rotR θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  have hdet : (rotR θ : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_fin_two, rotR_apply, rotR_apply, rotR_apply, rotR_apply]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  refine ⟨hdet, ?_, fun x y => ?_⟩
  · rw [hdet, norm_one]
  · rw [rotR_apply, rotR_apply, rotR_apply, rotR_apply]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

variable {w : InfinitePlace K} (hw : w.IsReal)

theorem norm_ringEquivRealOfIsReal_symm (x : ℝ) : ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  conv_rhs => rw [← (ringEquivRealOfIsReal hw).apply_symm_apply x]
  exact (norm_ringEquivRealOfIsReal hw _).symm

def rotAt (θ : ℝ) : rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_ringEquivRealOfIsReal_symm hw) ⟨rotR θ, rotR_mem θ⟩

theorem map_rotAt (θ : ℝ) :
    rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) (rotAt hw θ) =
      ⟨rotR θ, rotR_mem θ⟩ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  show (ringEquivRealOfIsReal hw) ((ringEquivRealOfIsReal hw).symm ((rotR θ : Matrix (Fin 2) (Fin 2) ℝ) i j)) = _
  exact (ringEquivRealOfIsReal hw).apply_symm_apply _

theorem archWeightOneAt_rotAt (θ : ℝ) :
    ((archWeightOneAt hw (rotAt hw θ) : ℂˣ) : ℂ) = Complex.exp (θ * Complex.I) := by
  show ((archWeightOneℝ (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
    (rotAt hw θ)) : ℂˣ) : ℂ) = _
  rw [map_rotAt]
  show firstRowℂ (rotR θ) = _
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]; rfl
  · rw [Complex.exp_ofReal_mul_I_im]; rfl

theorem archWeightCharAt_rotAt (n : ℤ) (θ : ℝ) :
    ((archWeightCharAt hw n (rotAt hw θ) : ℂˣ) : ℂ) = Complex.exp (n * (θ * Complex.I)) := by
  rw [Complex.exp_int_mul, ← archWeightOneAt_rotAt hw θ]
  show (((zpowGroupHom n) (archWeightOneAt hw (rotAt hw θ)) : ℂˣ) : ℂ) = _
  rw [zpowGroupHom_apply, Units.val_zpow_eq_zpow_val]

theorem exp_I_ne_one : Complex.exp Complex.I ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have him := congrArg Complex.im hn
  simp only [Complex.I_im, Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero,
    add_zero, mul_one, zero_add] at him

  have hpos : (0 : ℝ) < (n : ℝ) := by nlinarith [Real.pi_pos]
  have hn1 : (1 : ℤ) ≤ n := by have := Int.cast_pos.1 hpos; omega
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  nlinarith [Real.pi_gt_three]

end Rotation
p2m_reactivate "P2MW.S_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero.KtR"

section Ortho

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

variable {w : InfinitePlace K} (hw : w.IsReal)

theorem setIntegral_mul_conj_eq_zero_of_ne {α β : ℝ} {𝓕 : Set (AdelicGL2 (𝓞 K) K)}
    (h𝓕s : 𝓕 ⊆ slab K α β)
    (h𝓕 : IsFundamentalDomain (↥(Γp K)) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)))
    {n m : ℤ} (hnm : n ≠ m) (f g : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * x) = f x)
    (hg : ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K), g (globalPoints (𝓞 K) K γ * x) = g x)
    (hfw : HasArchCharacterAt₀ K w (archWeightCharAt hw n) f)
    (hgw : HasArchCharacterAt₀ K w (archWeightCharAt hw m) g) :
    ∫ x in 𝓕, f x * conj (g x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  set θ : ℝ := (((n - m : ℤ) : ℝ))⁻¹ with hθ
  set k : rowIsometrySubgroup₀ w.Completion := rotAt hw θ with hk
  have hF : ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K),
      (fun x => f x * conj (g x)) (globalPoints (𝓞 K) K γ * x) = (fun x => f x * conj (g x)) x := fun γ x => by
    simp only [hf γ x, hg γ x]
  have hT := setIntegral_comp_mul_incl_eq k α β h𝓕s h𝓕 (fun x => f x * conj (g x)) hF
  have hd : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hnm
  have hc : Complex.exp (n * (θ * Complex.I)) * conj (Complex.exp (m * (θ * Complex.I))) = Complex.exp Complex.I := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
    have hθ' : ((n : ℂ) - (m : ℂ)) * (θ : ℂ) = 1 := by
      have : ((n - m : ℤ) : ℝ) * θ = 1 := mul_inv_cancel₀ hd
      have h2 : (((n - m : ℤ) : ℝ) : ℂ) * ((θ : ℝ) : ℂ) = 1 := by exact_mod_cast this
      push_cast at h2
      exact h2
    linear_combination Complex.I * hθ'
  have hW : ∀ x : AdelicGL2 (𝓞 K) K, f (x * incl w k) * conj (g (x * incl w k)) = Complex.exp Complex.I * (f x * conj (g x)) := by
    intro x
    rw [show f (x * incl w k) = (archWeightCharAt hw n k : ℂ) * f x from hfw k x,
      show g (x * incl w k) = (archWeightCharAt hw m k : ℂ) * g x from hgw k x, map_mul,
      hk, archWeightCharAt_rotAt hw n θ, archWeightCharAt_rotAt hw m θ, ← hc]
    ring
  simp_rw [hW] at hT
  rw [integral_const_mul] at hT
  have h := sub_eq_zero.2 hT
  rw [← sub_one_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 exp_I_ne_one)

end Ortho
p2m_reactivate "P2MW.S_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero.KtR"

end KtR
p2m_reactivate "P2MW.S_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero.KtR"

namespace KtR

variable {K : Type} [Field K] [NumberField K]

section Parseval

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

variable {w : InfinitePlace K} (hw : w.IsReal)

theorem integral_normsq_sum_smul {α β : ℝ} {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ slab K α β)
    (h𝓕 : IsFundamentalDomain (↥(Γp K)) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)))
    (hfin : adelicGLHaar (Fin 2) (𝓞 K) K 𝓕 < ⊤)
    (ψ : ℤ → AdelicGL2 (𝓞 K) K → ℂ)
    (hinv : ∀ (n : ℤ) (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), ψ n (globalPoints (𝓞 K) K γ * g) = ψ n g)
    (hcont : ∀ n : ℤ, Continuous (ψ n))
    (hwt : ∀ n : ℤ, HasArchCharacterAt₀ K w (archWeightCharAt hw n) (ψ n))
    {B : ℝ} (hB : ∀ (n : ℤ) (g : AdelicGL2 (𝓞 K) K), g ∈ slab K α β → ‖ψ n g‖ ≤ B)
    (s : Finset ℤ) (a : ℤ → ℂ) :
    ∫ g in 𝓕, ‖(∑ n ∈ s, a n • ψ n) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∑ n ∈ s, ‖a n‖ ^ 2 * ∫ g in 𝓕, ‖ψ n g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have I : ∀ n m : ℤ, Integrable (fun g => ψ n g * conj (ψ m g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕) :=
    fun n m => integrable_mul_conj h𝓕m h𝓕s hfin (hcont n) (hcont m) (hB n) (hB m)
  have P : ∀ n m : ℤ, n ≠ m → ∫ g in 𝓕, ψ n g * conj (ψ m g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 :=
    fun n m hnm => setIntegral_mul_conj_eq_zero_of_ne hw h𝓕s h𝓕 hnm (ψ n) (ψ m) (hinv n) (hinv m) (hwt n) (hwt m)
  apply Complex.ofReal_injective
  rw [← setIntegral_mul_conj_self]
  have e1 : ∀ g : AdelicGL2 (𝓞 K) K, (∑ n ∈ s, a n • ψ n) g * conj ((∑ n ∈ s, a n • ψ n) g) =
      ∑ n ∈ s, ∑ m ∈ s, (a n * conj (a m)) * (ψ n g * conj (ψ m g)) := by
    intro g
    rw [Finset.sum_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  simp_rw [e1]
  rw [integral_finset_sum _ fun n _ => integrable_finset_sum _ fun m _ => (I n m).const_mul _]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_finset_sum _ fun m _ => (I n m).const_mul _]
  rw [Finset.sum_eq_single_of_mem n hn fun m _ hmn => by rw [integral_const_mul, P n m (Ne.symm hmn), mul_zero]]
  rw [integral_const_mul, setIntegral_mul_conj_self, Complex.mul_conj']

end Parseval
p2m_reactivate "P2MW.S_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero.KtR"

end KtR
p2m_reactivate "P2MW.S_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero.KtR"

open KtR in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (w : InfinitePlace K) (hw : w.IsReal) (N : ℕ)
    (ψ : ℤ → AdelicGL2 (𝓞 K) K → ℂ)
    (hinv : ∀ (n : ℤ) (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), ψ n (globalPoints (𝓞 K) K γ * g) = ψ n g)
    (hcont : ∀ n : ℤ, Continuous (ψ n))
    (hwt : ∀ n : ℤ, HasArchCharacterAt₀ K w (archWeightCharAt hw n) (ψ n))
    (hbdd : ∃ B : ℝ, ∀ (n : ℤ) (g : AdelicGL2 (𝓞 K) K),
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖ψ n g‖ ≤ B) :
    eLpNorm (∑ n ∈ Finset.Icc (-(N : ℤ)) N, (Complex.I * (n : ℂ)) • ψ n) 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
      (N : ENNReal) * eLpNorm (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ψ n) 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel _ _ _
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨𝓕, h𝓕m, h𝓕s, h𝓕, hres, hfin⟩ := exists_measurable_fd (K := K) α β hα hαβ
  set s : Finset ℤ := Finset.Icc (-(N : ℤ)) N with hs
  have hB' : ∀ (n : ℤ) (g : AdelicGL2 (𝓞 K) K), g ∈ slab K α β → ‖ψ n g‖ ≤ B := hB

  have hT := integral_normsq_sum_smul hw h𝓕m h𝓕s h𝓕 hfin ψ hinv hcont hwt hB' s (fun n => Complex.I * (n : ℂ))
  have hS := integral_normsq_sum_smul hw h𝓕m h𝓕s h𝓕 hfin ψ hinv hcont hwt hB' s (fun _ => 1)
  have eS : (∑ n ∈ s, (fun _ : ℤ => (1 : ℂ)) n • ψ n) = ∑ n ∈ s, ψ n := by simp only [one_smul]
  rw [eS] at hS
  set XT := ∫ g in 𝓕, ‖(∑ n ∈ s, (Complex.I * (n : ℂ)) • ψ n) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hXT
  set XS := ∫ g in 𝓕, ‖(∑ n ∈ s, ψ n) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hXS
  have hXn : ∀ n, 0 ≤ ∫ g in 𝓕, ‖ψ n g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := fun n =>
    integral_nonneg fun g => by positivity
  have hle : XT ≤ (N : ℝ) ^ 2 * XS := by
    rw [hT, hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' : ‖Complex.I * (n : ℂ)‖ ^ 2 ≤ (N : ℝ) ^ 2 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
      rw [Finset.mem_Icc] at hn
      have : |(n : ℝ)| ≤ (N : ℝ) := by
        rw [← Int.cast_abs]; exact_mod_cast abs_le.2 ⟨hn.1, hn.2⟩
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [norm_one, one_pow, one_mul]
    exact mul_le_mul_of_nonneg_right hn' (hXn n)
  have hXS0 : 0 ≤ XS := integral_nonneg fun g => by positivity
  have hXT0 : 0 ≤ XT := integral_nonneg fun g => by positivity

  have cT : Continuous (∑ n ∈ s, (Complex.I * (n : ℂ)) • ψ n) := by
    have h : Continuous fun g => ∑ n ∈ s, (Complex.I * (n : ℂ)) • ψ n g :=
      continuous_finsetSum s fun n _ => by
        simpa only [Pi.smul_def] using (hcont n).const_smul (Complex.I * (n : ℂ))
    convert h using 1
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply]
  have cS : Continuous (∑ n ∈ s, ψ n) := by
    have h : Continuous fun g => ∑ n ∈ s, ψ n g := continuous_finsetSum s fun n _ => hcont n
    convert h using 1
    funext g
    simp only [Finset.sum_apply]
  have bT : ∀ g, g ∈ 𝓕 → ‖(∑ n ∈ s, (Complex.I * (n : ℂ)) • ψ n) g‖ ≤ ∑ n ∈ s, ‖Complex.I * (n : ℂ)‖ * B := by
    intro g hg
    rw [Finset.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hB n g (h𝓕s hg)) (norm_nonneg _)
  have bS : ∀ g, g ∈ 𝓕 → ‖(∑ n ∈ s, ψ n) g‖ ≤ ∑ n ∈ s, B := by
    intro g hg
    rw [Finset.sum_apply]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => hB n g (h𝓕s hg))
  rw [← hres, eLpNorm_two_eq_sqrt h𝓕m hfin cT bT, eLpNorm_two_eq_sqrt h𝓕m hfin cS bS,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc Real.sqrt XT ≤ Real.sqrt ((N : ℝ) ^ 2 * XS) := Real.sqrt_le_sqrt hle
    _ = (N : ℝ) * Real.sqrt XS := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

end
p2m_reactivate "P2MW.S_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero.KtR"

end S_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero
end P2MW
export P2MW.S_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasArchCharacterAtZero (solution)
