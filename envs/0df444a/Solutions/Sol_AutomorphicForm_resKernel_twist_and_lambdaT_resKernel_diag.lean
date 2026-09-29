-- Prove2me | solution 1 for AutomorphicForm.resKernel_twist_and_lambdaT_resKernel_diag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ac4e29e6-b310-59e7-8993-1ae0d60464e8

import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_resKernel_twist_and_lambdaT_resKernel_diag
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : MeasureTheory.Measure (AdeleRing (𝓞 K) K)ˣ) (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (ξK ξ₀K : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (w : ℝ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (_hξ₀ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ξ₀K ⟨z, Subgroup.mem_top z⟩ = ξK ⟨z, Subgroup.mem_top z⟩ * cpowChar αm hαm (((-w : ℝ) : ℂ)) z),
    (∀ x y : AdelicGL2 (𝓞 K) K,
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y)) =
      ((((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x)) ^ (w / 2) : ℝ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y)) ^ (w / 2) : ℝ) : ℂ)⁻¹) *
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξ₀K χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, (f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y))) ∧
    (∀ (R : ℝ) (x : AdelicGL2 (𝓞 K) K),
      (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x) =
      (if NumberField.AdelicHeight.adelicHeight K x ≤ Real.exp R then 1 else 0) * (((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
        ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
          (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))) ∧
    (∀ R : ℝ, IntegrableOn (fun x : AdelicGL2 (𝓞 K) K =>
      (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x)) (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  intro αm hαm hξ₀
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  have hαI : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((αm z : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm K z := fun z => rfl
  have hpos := NumberField.TateGlobal.ideleNorm_pos (F := K)

  let τ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := cpowChar αm hαm (((-(w / 2) : ℝ)) : ℂ)
  have hτv : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((τ z : ℂˣ) : ℂ) =
      (((NumberField.TateGlobal.ideleNorm K z) ^ (w / 2) : ℝ) : ℂ)⁻¹ := by
    intro z
    show (((αm z : ℝˣ) : ℝ) : ℂ) ^ (((-(w / 2) : ℝ)) : ℂ) = _
    rw [hαI, ← Complex.ofReal_cpow (hpos z).le, Real.rpow_neg (hpos z).le, Complex.ofReal_inv]
  have hNz : ∀ z : (AdeleRing (𝓞 K) K)ˣ, (((NumberField.TateGlobal.ideleNorm K z) ^ (w / 2) : ℝ) : ℂ) ≠ 0 := by
    intro z; exact_mod_cast (Real.rpow_pos_of_pos (hpos z) _).ne'
  have hτ1 : ∀ a : Kˣ, τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) = 1 := by
    intro a
    apply Units.ext
    rw [hτv, Units.val_one]
    have h := NumberField.AdeleRing.distribHaarChar_algebraMap K a
    have h' : NumberField.TateGlobal.ideleNorm K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) a) = 1 := by
      have h'' := congrArg (fun u : ℝ≥0 => (u : ℝ)) h
      simpa [NumberField.TateGlobal.ideleNorm] using h''
    rw [h']; simp
  have hτc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((τ z : ℂˣ) : ℂ) := by
    simp_rw [hτv]
    refine (Complex.continuous_ofReal.comp ?_).inv₀ (fun z => hNz z)
    exact (NumberField.TateGlobal.continuous_ideleNorm K).rpow_const (fun z => Or.inl (hpos z).ne')

  have hττ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, τ z * τ z = cpowChar αm hαm (((-w : ℝ)) : ℂ) z := by
    intro z
    apply Units.ext
    rw [Units.val_mul]
    show (((αm z : ℝˣ) : ℝ) : ℂ) ^ (((-(w / 2) : ℝ)) : ℂ) * (((αm z : ℝˣ) : ℝ) : ℂ) ^ (((-(w / 2) : ℝ)) : ℂ) =
      (((αm z : ℝˣ) : ℝ) : ℂ) ^ (((-w : ℝ)) : ℂ)
    rw [← Complex.cpow_add _ _ (by exact_mod_cast (hαm z).ne')]
    congr 1; push_cast; ring

  set Sξ : Set ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)} with hSξ
  set Sξ₀ : Set ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξ₀K χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)} with hSξ₀
  have hmem : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, χ ∈ Sξ ↔ χ * τ ∈ Sξ₀ := by
    intro χ
    simp only [hSξ, hSξ₀, Set.mem_setOf_eq, SquaresToXi, MonoidHom.mul_apply]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun z => ?_, fun z hz => ?_, ?_⟩
      · rw [mul_pow, h1 z, pow_two, hττ, hξ₀ z]
      · obtain ⟨a, rfl⟩ := hz
        rw [h2 _ ⟨a, rfl⟩, hτ1 a, one_mul]
      · simp_rw [Units.val_mul]; exact h3.mul hτc
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun z => ?_, fun z hz => ?_, ?_⟩
      · have := h1 z
        rw [mul_pow, pow_two (τ _), hττ, hξ₀ z] at this
        exact mul_right_cancel this
      · obtain ⟨a, rfl⟩ := hz
        have := h2 _ ⟨a, rfl⟩
        rwa [hτ1 a, mul_one] at this
      · have h4 : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z * τ z : ℂˣ) : ℂ) * (((τ z : ℂˣ) : ℂ))⁻¹ :=
          h3.mul (hτc.inv₀ (fun z => by rw [hτv]; exact inv_ne_zero (hNz z)))
        refine h4.congr (fun z => ?_)
        rw [Units.val_mul, mul_assoc, mul_inv_cancel₀ (by rw [hτv]; exact inv_ne_zero (hNz z)), mul_one]
  have hbij : Set.BijOn (fun χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ => χ * τ) Sξ Sξ₀ := by
    refine ⟨fun χ hχ => (hmem χ).1 hχ, fun χ _ χ' _ h => mul_right_cancel h, fun χ₀ hχ₀ => ?_⟩
    have hcancel : χ₀ * τ⁻¹ * τ = χ₀ := by
      ext1 z
      simp [MonoidHom.mul_apply, mul_assoc]
    refine ⟨χ₀ * τ⁻¹, ?_, hcancel⟩
    show χ₀ * τ⁻¹ ∈ Sξ
    rw [hmem, hcancel]; exact hχ₀
  have hdetu : ∀ q : AdeleRing (𝓞 K) K, Matrix.GeneralLinearGroup.det (AutomorphicForm.unipotentGL2 q) = 1 := by
    intro q; ext; simp [Matrix.det_fin_two_of]
  have hNg : ∀ g : AdelicGL2 (𝓞 K) K, (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ) ≠ 0 := fun g => hNz _

  have h1 : ∀ x y : AdelicGL2 (𝓞 K) K,
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sξ),
        (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y)) =
      ((((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x)) ^ (w / 2) : ℝ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y)) ^ (w / 2) : ℝ) : ℂ)⁻¹) *
      ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sξ₀),
        (∫ g, (f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y) := by
    intro x y
    rw [mul_finsum_mem]
    refine finsum_mem_eq_of_bijOn (fun χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ => χ * τ) hbij (fun χ _ => ?_)
    have hcd : ∀ g : AdelicGL2 (𝓞 K) K, chiDet (𝓞 K) K (χ * τ) g = chiDet (𝓞 K) K χ g * ((((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ))⁻¹ := by
      intro g; simp only [AutomorphicForm.chiDet, MonoidHom.mul_apply, Units.val_mul, hτv]
    have hcdi : ∀ g : AdelicGL2 (𝓞 K) K, chiDet (𝓞 K) K (χ * τ)⁻¹ g = chiDet (𝓞 K) K χ⁻¹ g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ) := by
      intro g
      simp only [AutomorphicForm.chiDet, mul_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
        Units.val_inv_eq_inv_val, hτv, inv_inv]
    have hI : (∫ g, (f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) * chiDet (𝓞 K) K (χ * τ) g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        ∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
      congr 1; funext g
      rw [hcd g]; field_simp [hNg g]
    rw [hI, hcd x, hcdi y]
    field_simp [hNg x, hNg y]

  have hcc : ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (x : AdelicGL2 (𝓞 K) K), chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ x = 1 := by
    intro χ x
    simp only [AutomorphicForm.chiDet, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact mul_inv_cancel₀ (Units.ne_zero _)
  have hprobν : MeasureTheory.IsProbabilityMeasure
      ((productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν) :=
    NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox K
  haveI := hprobν
  have h2 : ∀ (R : ℝ) (x : AdelicGL2 (𝓞 K) K),
      (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sξ),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x) =
      (if NumberField.AdelicHeight.adelicHeight K x ≤ Real.exp R then 1 else 0) * (((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
        ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sξ),
          (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by
    intro R x
    rw [AutomorphicForm.lambdaT_apply]
    have hdiag : ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
        ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sξ),
          (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ x) =
        ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
        ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sξ),
          (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
      simp only [hcc, mul_one]
    by_cases hx : x ∈ AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
    · rw [Set.indicator_of_mem hx]
      simp only [AutomorphicForm.constantTerm, AutomorphicForm.constantTermIntegrand, AutomorphicForm.chiDet, map_mul, hdetu,
        one_mul]
      rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul, sub_self]
      rw [AutomorphicForm.mem_highSet_iff] at hx
      rw [if_neg (not_le.mpr hx), zero_mul]
    · rw [Set.indicator_of_notMem hx, sub_zero, hdiag]
      rw [AutomorphicForm.mem_highSet_iff, not_lt] at hx
      rw [if_pos hx, one_mul]

  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  obtain ⟨-, -, -, hΦs, hΦ⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  haveI hfinΦ : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ
      (AutomorphicForm.canonicalTruncationDomain K α β) hΦ
    rwa [Set.inter_eq_left.mpr hΦs] at h
  have h3 : ∀ R : ℝ, IntegrableOn (fun x : AdelicGL2 (𝓞 K) K =>
      (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sξ),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x)) (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro R
    have hmeas : MeasurableSet {x : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K x ≤ Real.exp R} :=
      (isClosed_le (NumberField.AdelicHeight.continuous_adelicHeight K) continuous_const).measurableSet
    have hf3 : (fun x : AdelicGL2 (𝓞 K) K =>
      (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sξ),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x)) =
      Set.indicator {x : AdelicGL2 (𝓞 K) K | NumberField.AdelicHeight.adelicHeight K x ≤ Real.exp R}
        (fun _ => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
          ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ Sξ),
            (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by
      funext x
      rw [h2 R x]
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs <;> simp
    rw [IntegrableOn, hf3]
    exact (integrable_const _).indicator hmeas
  exact ⟨h1, h2, h3⟩

end S_AutomorphicForm_resKernel_twist_and_lambdaT_resKernel_diag
end P2MW
export P2MW.S_AutomorphicForm_resKernel_twist_and_lambdaT_resKernel_diag (solution)
