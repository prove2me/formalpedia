-- Prove2me | solution 1 for AutomorphicForm.isSlabProfile_levelTypeAverage_and_eq_sum_integral_of_kernel_maximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/294a11ee-d70e-5a1a-b1ac-c0255df74251

import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isSlabProfile_levelTypeAverage_and_eq_sum_integral_of_kernel_maximalCompact
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm NumberField.AdelicHeight

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (κ : ↥(adelicMaximalCompact K) → ℂ) (_hκ : Continuous κ)
      (P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
      (_hP : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
        P φ g = ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g),
    (AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK (P ψ)) ∧
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        P ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, P (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g) := by
  classical
  intro αm hαm κ hκ P hP ιP instP μP νP hμ hν hμic hνic hμc hμν rP hr hdist
    ψf hψf hψjc hψhol hψK hψsm hψKu hνc hψdec ψ hψ hψrep
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  set μK := maximalCompactHaar K with hμK
  have hξu1 : ∀ z : ↥(productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z, ‖((ξK z : ℂˣ) : ℂ)‖ = 1 := fun z => hξu z

  have hdetc : Continuous fun k : adelicMaximalCompact K =>
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K)) :=
    (NumberField.TateGlobal.continuous_ideleNorm_det K).comp continuous_subtype_val
  obtain ⟨kmin, -, hmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hdetc.continuousOn
  obtain ⟨kmax, -, hmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hdetc.continuousOn
  set m := NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (kmin : AdelicGL2 (𝓞 K) K)) with hm
  set M := NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (kmax : AdelicGL2 (𝓞 K) K)) with hM
  have hm0 : 0 < m := NumberField.TateGlobal.ideleNorm_pos _
  have hmM : ∀ k : adelicMaximalCompact K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K)) ∈ Set.Icc m M :=
    fun k => ⟨hmin (Set.mem_univ k), hmax (Set.mem_univ k)⟩
  have hψm : Measurable ψ := hψ.measurable
  have hκi : Integrable (fun k : adelicMaximalCompact K => ‖κ k‖) μK :=
    hκ.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPψ : P ψ = fun h => ∫ k, κ k * ψ (h * (k : AdelicGL2 (𝓞 K) K)) ∂μK := funext (hP ψ)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    rw [hPψ]
    have hsm : StronglyMeasurable (Function.uncurry fun (h : AdelicGL2 (𝓞 K) K) (k : adelicMaximalCompact K) =>
        κ k * ψ (h * (k : AdelicGL2 (𝓞 K) K))) :=
      ((hκ.measurable.comp measurable_snd).mul
        (hψm.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).measurable)).stronglyMeasurable
    exact hsm.integral_prod_right.measurable
  · intro x h
    simp only [hP, mul_assoc, hψ.unipotent_mul]
  · intro γ hγ h
    simp only [hP, mul_assoc, hψ.borel_mul γ hγ]
  · intro z h
    simp only [hP, mul_assoc, hψ.central_transform]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    ring
  · intro d₁ d₂ hd₁
    obtain ⟨C, hC⟩ := hψ.bounded_on_slab (d₁ * m) (d₂ * M) (mul_pos hd₁ hm0)
    refine ⟨max C 0 * ∫ k, ‖κ k‖ ∂μK, fun h hh => ?_⟩
    rw [hP]
    calc ‖∫ k, κ k * ψ (h * (k : AdelicGL2 (𝓞 K) K)) ∂μK‖ ≤ ∫ k, ‖κ k * ψ (h * (k : AdelicGL2 (𝓞 K) K))‖ ∂μK :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ k, max C 0 * ‖κ k‖ ∂μK := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun k => norm_nonneg _) (hκi.const_mul _)
            (Filter.Eventually.of_forall fun k => ?_)
          show ‖κ k * ψ (h * (k : AdelicGL2 (𝓞 K) K))‖ ≤ max C 0 * ‖κ k‖
          rw [norm_mul, mul_comm]
          refine mul_le_mul_of_nonneg_right ((hC _ ?_).trans (le_max_left _ _)) (norm_nonneg _)
          rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
          exact ⟨mul_le_mul hh.1 (hmM k).1 hm0.le (hd₁.le.trans hh.1),
            mul_le_mul hh.2 (hmM k).2 (NumberField.TateGlobal.ideleNorm_pos _).le
              (hd₁.le.trans (hh.1.trans hh.2))⟩
      _ = max C 0 * ∫ k, ‖κ k‖ ∂μK := integral_const_mul _ _
  · obtain ⟨a, b, ha, hband⟩ := hψ.height_band
    refine ⟨a, b, ha, fun h hh => ?_⟩
    have hex : ∃ k : adelicMaximalCompact K, ψ (h * (k : AdelicGL2 (𝓞 K) K)) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hh
      rw [hP]
      exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun k => by
        show κ k * ψ (h * (k : AdelicGL2 (𝓞 K) K)) = (0 : adelicMaximalCompact K → ℂ) k
        rw [hcon k, mul_zero, Pi.zero_apply])
    obtain ⟨k, hψk⟩ := hex
    have hhk := hband _ hψk
    rwa [NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact K h (k : AdelicGL2 (𝓞 K) K) k.2] at hhk
  ·
    intro σ' g
    have hC : IsCompact ((fun k : AdelicGL2 (𝓞 K) K => g * k) '' (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K))) :=
      (isCompact_adelicMaximalCompact K).image (continuous_const_mul g)
    have hmem : ∀ k : adelicMaximalCompact K, g * (k : AdelicGL2 (𝓞 K) K) ∈ (fun k : AdelicGL2 (𝓞 K) K => g * k) '' (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) :=
      fun k => ⟨k, k.2, rfl⟩

    have hprod : ∀ e : ιP, Integrable (Function.uncurry fun (k : adelicMaximalCompact K) (t : ℝ) =>
        κ k * ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 K) K))) (μK.prod MeasureTheory.volume) := by
      intro e
      obtain ⟨mb, hmi, ⟨B, hB⟩, hmb⟩ := hψdec e 2 |σ'| _ hC
      have hmeas : AEStronglyMeasurable (Function.uncurry fun (k : adelicMaximalCompact K) (t : ℝ) =>
          κ k * ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 K) K))) (μK.prod MeasureTheory.volume) := by
        refine Continuous.aestronglyMeasurable ?_
        have h2 : Continuous fun a : adelicMaximalCompact K × ℝ =>
            (((σ' : ℂ) + (a.2 : ℂ) * Complex.I), g * (a.1 : AdelicGL2 (𝓞 K) K)) :=
          (continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)).prodMk
            (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
        exact (hκ.comp continuous_fst).mul ((hψjc e).comp h2)
      refine Integrable.mono' (hκi.mul_prod hmi) hmeas (Filter.Eventually.of_forall fun p => ?_)
      have h1 := hmb σ' le_rfl p.2 (g * (p.1 : AdelicGL2 (𝓞 K) K)) (hmem p.1)
      have hmt : 0 ≤ mb p.2 := le_trans (by positivity) h1
      have h2 : ‖ψf e ((σ' : ℂ) + (p.2 : ℂ) * Complex.I) (g * (p.1 : AdelicGL2 (𝓞 K) K))‖ ≤ mb p.2 := by
        have h3 : (1 : ℝ) ≤ (1 + |p.2|) ^ 2 := by nlinarith [abs_nonneg p.2]
        calc ‖ψf e ((σ' : ℂ) + (p.2 : ℂ) * Complex.I) (g * (p.1 : AdelicGL2 (𝓞 K) K))‖
            = 1 * ‖ψf e ((σ' : ℂ) + (p.2 : ℂ) * Complex.I) (g * (p.1 : AdelicGL2 (𝓞 K) K))‖ := (one_mul _).symm
          _ ≤ (1 + |p.2|) ^ 2 * ‖ψf e ((σ' : ℂ) + (p.2 : ℂ) * Complex.I) (g * (p.1 : AdelicGL2 (𝓞 K) K))‖ :=
              mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          _ ≤ mb p.2 := h1
      show ‖κ p.1 * ψf e ((σ' : ℂ) + (p.2 : ℂ) * Complex.I) (g * (p.1 : AdelicGL2 (𝓞 K) K))‖ ≤ ‖κ p.1‖ * mb p.2
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    rw [hP]
    have hstep1 : (fun k : adelicMaximalCompact K => κ k * ψ (g * (k : AdelicGL2 (𝓞 K) K))) =
        fun k => ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, κ k * ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 K) K)) := by
      funext k
      rw [hψrep σ' (g * (k : AdelicGL2 (𝓞 K) K)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [integral_const_mul]
      ring
    rw [hstep1, integral_finsetSum _ fun e _ => ?_]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [integral_const_mul, integral_integral_swap (hprod e)]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      exact (hP _ _).symm
    · exact ((hprod e).integral_prod_left).const_mul _

end S_AutomorphicForm_isSlabProfile_levelTypeAverage_and_eq_sum_integral_of_kernel_maximalCompact
end P2MW
export P2MW.S_AutomorphicForm_isSlabProfile_levelTypeAverage_and_eq_sum_integral_of_kernel_maximalCompact (solution)
