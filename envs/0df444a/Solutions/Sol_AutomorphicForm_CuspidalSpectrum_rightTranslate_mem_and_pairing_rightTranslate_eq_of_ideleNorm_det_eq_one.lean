-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/17e2c0be-5ac9-54af-acb0-c4945460baef

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ contMemberSubmodule F Φ₀ ξ) (hψ : ψ ∈ contMemberSubmodule F Φ₀ ξ)
    (y : AdelicGL2 (𝓞 F) F)
    (hy : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) = 1) :
    rightTranslate F y φ ∈ contMemberSubmodule F Φ₀ ξ ∧
    rightTranslate F y⁻¹ ψ ∈ contMemberSubmodule F Φ₀ ξ ∧
    pairing F Φ₀ σ (rightTranslate F y φ) ψ = pairing F Φ₀ σ φ (rightTranslate F y⁻¹ ψ) := by
  classical
  haveI hBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI hHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI hRinv : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set S : Set (AdelicGL2 (𝓞 F) F) := detNormSlab F α β with hS

  obtain ⟨hφlx, hφ2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1
  obtain ⟨hψlx, hψ2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ ψ).mp hψ.1
  have hφc : Continuous φ := hφ.2
  have hψc : Continuous ψ := hψ.2

  have hdet_mul : ∀ x z : AdelicGL2 (𝓞 F) F, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (x * z)) = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det z) := by
    intro x z; rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
  have hone : NumberField.TateGlobal.ideleNorm F (1 : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
    have h1 := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
    rw [mul_one] at h1
    exact (mul_right_eq_self₀.mp h1.symm).resolve_right (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hinv : ∀ z : AdelicGL2 (𝓞 F) F, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det z) = 1 → NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det z⁻¹) = 1 := by
    intro z hz
    have h := hdet_mul z⁻¹ z
    rw [inv_mul_cancel, map_one, hone, hz, mul_one] at h
    exact h.symm
  have hyinv : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y⁻¹) = 1 := hinv y hy
  have hS_mul : ∀ z : AdelicGL2 (𝓞 F) F, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det z) = 1 → ∀ x, x * z ∈ S ↔ x ∈ S := by
    intro z hz x
    simp only [hS, mem_detNormSlab, hdet_mul, hz, mul_one]
  have hS_meas : MeasurableSet S :=
    (isClosed_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det F)).measurableSet
  have hΓ : ∀ g : ↥(globalPoints (𝓞 F) F).range, ∃ γ₀, (g : AdelicGL2 (𝓞 F) F) = globalPoints (𝓞 F) F γ₀ := fun g => by
    obtain ⟨γ₀, h⟩ := MonoidHom.mem_range.mp g.2
    exact ⟨γ₀, h.symm⟩
  have hWΓ : ∀ (g : ↥(globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F), NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det ((g : AdelicGL2 (𝓞 F) F) * x)) = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) := by
    intro g x
    obtain ⟨γ₀, hg⟩ := hΓ g
    rw [hdet_mul, hg, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  have hφΓ : ∀ (g : ↥(globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F), φ ((g : AdelicGL2 (𝓞 F) F) * x) = φ x := by
    intro g x; obtain ⟨γ₀, hg⟩ := hΓ g; rw [hg]; exact hφlx.left_invariant γ₀ x
  have hψΓ : ∀ (g : ↥(globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F), ψ ((g : AdelicGL2 (𝓞 F) F) * x) = ψ x := by
    intro g x; obtain ⟨γ₀, hg⟩ := hΓ g; rw [hg]; exact hψlx.left_invariant γ₀ x

  haveI hSMul : SMulInvariantMeasure (↥(globalPoints (𝓞 F) F).range) (AdelicGL2 (𝓞 F) F) (μ.restrict S) := by
    refine ⟨fun g s hs => ?_⟩
    have hset : (fun x : AdelicGL2 (𝓞 F) F => g • x) ⁻¹' s ∩ S = (fun x : AdelicGL2 (𝓞 F) F => (g : AdelicGL2 (𝓞 F) F) * x) ⁻¹' (s ∩ S) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, hS, mem_detNormSlab, hWΓ]
    have hmeas : MeasurableSet ((fun x : AdelicGL2 (𝓞 F) F => g • x) ⁻¹' s) := (measurable_const_mul (g : AdelicGL2 (𝓞 F) F)) hs
    rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs, hset, measure_preimage_mul]
  haveI hcount : Countable ↥(globalPoints (𝓞 F) F).range := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
    haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
      Function.Injective.countable fun _ _ h => Units.ext h
    have h : (((globalPoints (𝓞 F) F).range : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)).Countable := by
      rw [MonoidHom.coe_range]
      exact Set.countable_range _
    exact h.to_subtype

  have hpres : ∀ z : AdelicGL2 (𝓞 F) F, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det z) = 1 → MeasurePreserving (fun x => x * z) (μ.restrict S) (μ.restrict S) := by
    intro z hz
    refine ⟨measurable_mul_const z, ?_⟩
    have hpre : (fun x => x * z) ⁻¹' S = S := Set.ext fun x => hS_mul z hz x
    calc (μ.restrict S).map (fun x => x * z)
        = (μ.restrict ((fun x => x * z) ⁻¹' S)).map (fun x => x * z) := by rw [hpre]
      _ = (μ.map (fun x => x * z)).restrict S := (Measure.restrict_map (measurable_mul_const z) hS_meas).symm
      _ = μ.restrict S := by rw [map_mul_right_eq_self]
  have hFD : ∀ z : AdelicGL2 (𝓞 F) F, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det z) = 1 →
      IsFundamentalDomain (↥(globalPoints (𝓞 F) F).range) ((fun x => x * z) '' Φ₀) (μ.restrict S) := by
    intro z hz
    have h := hΦ₀.isFundamentalDomain.image_of_equiv (ν := μ.restrict S) (Equiv.mulRight z)
      (by simpa using (hpres z⁻¹ (hinv z hz)).quasiMeasurePreserving) (Equiv.refl _)
      (fun g x => by simp [Subgroup.smul_def, mul_assoc])
    simpa using h
  have hsub : ∀ z : AdelicGL2 (𝓞 F) F, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det z) = 1 → (fun x => x * z) '' Φ₀ ⊆ S := by
    rintro z hz _ ⟨x, hx, rfl⟩
    exact (hS_mul z hz x).mpr (hΦ₀.subset hx)
  have hres0 : (μ.restrict S).restrict Φ₀ = μ.restrict Φ₀ := by
    rw [Measure.restrict_restrict₀ hΦ₀.isFundamentalDomain.nullMeasurableSet, Set.inter_eq_left.mpr hΦ₀.subset]
  have hres1 : ∀ z : AdelicGL2 (𝓞 F) F, ∀ hz : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det z) = 1,
      (μ.restrict S).restrict ((fun x => x * z) '' Φ₀) = μ.restrict ((fun x => x * z) '' Φ₀) := by
    intro z hz
    rw [Measure.restrict_restrict₀ (hFD z hz).nullMeasurableSet, Set.inter_eq_left.mpr (hsub z hz)]

  have hmap : ∀ z : AdelicGL2 (𝓞 F) F, (μ.restrict Φ₀).map (MeasurableEquiv.mulRight z) = μ.restrict ((fun x => x * z) '' Φ₀) := by
    intro z
    have h := MeasurableEquiv.restrict_map (MeasurableEquiv.mulRight z) μ ((fun x => x * z) '' Φ₀)
    have hpre : (MeasurableEquiv.mulRight z) ⁻¹' ((fun x => x * z) '' Φ₀) = Φ₀ := by
      ext x
      simp only [MeasurableEquiv.coe_mulRight, Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨x', hx', h⟩
        rwa [← mul_right_cancel h]
      · exact fun hx => ⟨x, hx, rfl⟩
    rw [hpre] at h
    rw [← h]
    congr 1
    rw [MeasurableEquiv.coe_mulRight]
    exact map_mul_right_eq_self μ z
  have hcv_l : ∀ (z : AdelicGL2 (𝓞 F) F) (H : AdelicGL2 (𝓞 F) F → ℝ≥0∞),
      ∫⁻ x in Φ₀, H (x * z) ∂μ = ∫⁻ x in (fun x => x * z) '' Φ₀, H x ∂μ := by
    intro z H
    rw [← hmap z, lintegral_map_equiv]
    rfl
  have hcv_i : ∀ (z : AdelicGL2 (𝓞 F) F) (H : AdelicGL2 (𝓞 F) F → ℂ),
      ∫ x in Φ₀, H (x * z) ∂μ = ∫ x in (fun x => x * z) '' Φ₀, H x ∂μ := by
    intro z H
    rw [← hmap z, integral_map_equiv]
    rfl
  have hfd_l : ∀ (z : AdelicGL2 (𝓞 F) F), NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det z) = 1 → ∀ (H : AdelicGL2 (𝓞 F) F → ℝ≥0∞),
      (∀ (g : ↥(globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F), H (g • x) = H x) →
      ∫⁻ x in (fun x => x * z) '' Φ₀, H x ∂μ = ∫⁻ x in Φ₀, H x ∂μ := by
    intro z hz H hH
    rw [← hres0, ← hres1 z hz]
    exact (hFD z hz).setLIntegral_eq hΦ₀.isFundamentalDomain H hH
  have hfd_i : ∀ (z : AdelicGL2 (𝓞 F) F), NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det z) = 1 → ∀ (H : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (g : ↥(globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F), H (g • x) = H x) →
      ∫ x in (fun x => x * z) '' Φ₀, H x ∂μ = ∫ x in Φ₀, H x ∂μ := by
    intro z hz H hH
    rw [← hres0, ← hres1 z hz]
    exact (hFD z hz).setIntegral_eq hΦ₀.isFundamentalDomain hH

  have memR : ∀ (z : AdelicGL2 (𝓞 F) F), NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det z) = 1 → ∀ θ : AdelicGL2 (𝓞 F) F → ℂ, θ ∈ contMemberSubmodule F Φ₀ ξ →
      rightTranslate F z θ ∈ contMemberSubmodule F Φ₀ ξ := by
    intro z hz θ hθ
    obtain ⟨hθlx, hθ2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ θ).mp hθ.1
    have hθc : Continuous θ := hθ.2
    have hθzc : Continuous (rightTranslate F z θ) := hθc.comp (continuous_id.mul continuous_const)
    have hθΓ : ∀ (g : ↥(globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F), θ ((g : AdelicGL2 (𝓞 F) F) * x) = θ x := by
      intro g x; obtain ⟨γ₀, hg⟩ := hΓ g; rw [hg]; exact hθlx.left_invariant γ₀ x
    refine ⟨(mem_memberSubmodule_iff' F Φ₀ ξ _).mpr ⟨⟨fun γ x => ?_, fun c x => ?_⟩, ?_⟩, hθzc⟩
    · show θ (globalPoints (𝓞 F) F γ * x * z) = θ (x * z)
      rw [mul_assoc]; exact hθlx.left_invariant γ (x * z)
    · show θ (centralScalar (𝓞 F) F ((c : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F)ˣ) * x * z) =
        ((ξ c : ℂˣ) : ℂ) * θ (x * z)
      rw [mul_assoc]; exact hθlx.central_transform c (x * z)
    ·
      rw [memLp_two_iff_integrable_sq_norm hθzc.aestronglyMeasurable]
      have hint := (memLp_two_iff_integrable_sq_norm hθc.aestronglyMeasurable).mp hθ2
      refine ⟨(hθzc.norm.pow 2).aestronglyMeasurable, ?_⟩
      have hH : ∀ (g : ↥(globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F),
          (fun x => ‖‖θ x‖ ^ 2‖ₑ) (g • x) = (fun x => ‖‖θ x‖ ^ 2‖ₑ) x := by
        intro g x; simp only [Subgroup.smul_def, smul_eq_mul, hθΓ]
      have h1 := hcv_l z (fun x => ‖‖θ x‖ ^ 2‖ₑ)
      have h2 := hfd_l z hz (fun x => ‖‖θ x‖ ^ 2‖ₑ) hH
      show ∫⁻ x in Φ₀, ‖‖rightTranslate F z θ x‖ ^ 2‖ₑ ∂μ < ⊤
      simp only [rightTranslate_apply]
      rw [h1, h2]
      exact hint.2
  refine ⟨memR y hy φ hφ, memR y⁻¹ hyinv ψ hψ, ?_⟩

  set Hc : AdelicGL2 (𝓞 F) F → ℂ := fun x => φ x * conj (ψ (x * y⁻¹)) *
    ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) with hHc
  have hHΓ : ∀ (g : ↥(globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F), Hc (g • x) = Hc x := by
    intro g x
    have e1 : (g : AdelicGL2 (𝓞 F) F) * x * y⁻¹ = (g : AdelicGL2 (𝓞 F) F) * (x * y⁻¹) := mul_assoc _ _ _
    simp only [hHc, Subgroup.smul_def, smul_eq_mul, hφΓ, e1, hψΓ, hWΓ]
  unfold pairing
  rw [← hμ]
  calc ∫ x in Φ₀, rightTranslate F y φ x * conj (ψ x) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) ∂μ
      = ∫ x in Φ₀, Hc (x * y) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hHc, rightTranslate_apply, mul_inv_cancel_right, hdet_mul, hy, mul_one]
    _ = ∫ x in (fun x => x * y) '' Φ₀, Hc x ∂μ := hcv_i y Hc
    _ = ∫ x in Φ₀, Hc x ∂μ := hfd_i y hy Hc hHΓ
    _ = ∫ x in Φ₀, φ x * conj (rightTranslate F y⁻¹ ψ x) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hHc, rightTranslate_apply]

end S_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one (solution)
