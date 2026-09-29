-- Prove2me | solution 1 for AutomorphicForm.continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1a0a4a83-596e-5972-b2fc-90816e1b6790

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm LanglandsTunnell.RankinSelberg

theorem solution
    (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (h : AdelicGL2 (𝓞 F) F) :
    ((Continuous φ → Continuous fun g => φ (g * h) - φ g) ∧
    (IsRapidlyDecreasingOnSiegelSets F φ → IsRapidlyDecreasingOnSiegelSets F fun g => φ (g * h) - φ g) ∧
    ((∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g) →
      ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        (fun g => φ (g * h) - φ g) (globalPoints (𝓞 F) F γ * g) = (fun g => φ (g * h) - φ g) g) ∧
    (∀ ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ,
      (∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F), φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g) →
      ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        (fun g => φ (g * h) - φ g) (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * (fun g => φ (g * h) - φ g) g) ∧
    (∀ (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F),
      WhittakerCoefficientIntegrable F pins ψ φ α (g * h) → WhittakerCoefficientIntegrable F pins ψ φ α g →
        WhittakerCoefficientIntegrable F pins ψ (fun g => φ (g * h) - φ g) α g ∧
        whittakerCoefficient F pins ψ (fun g => φ (g * h) - φ g) α g =
          whittakerCoefficient F pins ψ φ α (g * h) - whittakerCoefficient F pins ψ φ α g) ∧
    (∀ (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (g : AdelicGL2 (𝓞 F) F),
      (∀ α : F, WhittakerCoefficientIntegrable F pins ψ φ α (g * h)) →
      (∀ α : F, WhittakerCoefficientIntegrable F pins ψ φ α g) →
      (Summable fun α : F => ‖whittakerCoefficient F pins ψ φ α (g * h)‖) →
      (Summable fun α : F => ‖whittakerCoefficient F pins ψ φ α g‖) →
        Summable fun α : F => ‖whittakerCoefficient F pins ψ (fun g => φ (g * h) - φ g) α g‖) ∧
    (∀ (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F)
      {β γ : Type} [Mul γ] (r : AdelicGL2 (𝓞 F) F → β) (f : AdelicGL2 (𝓞 F) F → γ) (h' : γ)
      (WA : β → ℂ) (Wf : γ → ℂ),
      (∀ g : AdelicGL2 (𝓞 F) F, r (g * h) = r g) → (∀ g : AdelicGL2 (𝓞 F) F, f (g * h) = f g * h') →
      (∀ g : AdelicGL2 (𝓞 F) F, WhittakerCoefficientIntegrable F pins ψ φ α g) →
      (∀ g : AdelicGL2 (𝓞 F) F, whittakerCoefficient F pins ψ φ α g = WA (r g) * Wf (f g)) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          whittakerCoefficient F pins ψ (fun g => φ (g * h) - φ g) α g = WA (r g) * (Wf (f g * h') - Wf (f g)))) := by
  have key : ∀ (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F),
      WhittakerCoefficientIntegrable F pins ψ φ α (g * h) → WhittakerCoefficientIntegrable F pins ψ φ α g →
        WhittakerCoefficientIntegrable F pins ψ (fun g => φ (g * h) - φ g) α g ∧
        whittakerCoefficient F pins ψ (fun g => φ (g * h) - φ g) α g =
          whittakerCoefficient F pins ψ φ α (g * h) - whittakerCoefficient F pins ψ φ α g := by
    intro pins ψ α g h1 h2
    have h1' : (letI := pins.nS; Integrable (fun x => φ (unipotentGL2 x * g * h) *
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) pins.ν) := by
      simpa only [WhittakerCoefficientIntegrable, mul_assoc] using h1
    have h2' : (letI := pins.nS; Integrable (fun x => φ (unipotentGL2 x * g) *
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) pins.ν) := h2
    constructor
    · show (letI := pins.nS; Integrable (fun x => (φ (unipotentGL2 x * g * h) - φ (unipotentGL2 x * g)) *
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) pins.ν)
      simp only [sub_mul]
      exact h1'.sub h2'
    · show (letI := pins.nS; ∫ x, (φ (unipotentGL2 x * g * h) - φ (unipotentGL2 x * g)) *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂pins.ν) =
        (letI := pins.nS; ∫ x, φ (unipotentGL2 x * (g * h)) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂pins.ν) -
        (letI := pins.nS; ∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂pins.ν)
      letI := pins.nS
      simp only [sub_mul, ← mul_assoc]
      exact integral_sub h1' h2'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hφ
    exact (hφ.comp (continuous_id.mul continuous_const)).sub hφ
  · intro hR c u t hc N
    obtain ⟨C₁, h₁⟩ := hR c u (t * h) hc N
    obtain ⟨C₂, h₂⟩ := hR c u t hc N
    refine ⟨|C₁| + |C₂|, fun g hg => ?_⟩
    have e1 := h₁ g hg
    have e2 := h₂ g hg
    rw [← mul_assoc] at e1
    set w := (1 + WindowedSiegel.archHeight F (glArch (𝓞 F) F g)) ^ N with hw
    show ‖φ (g * t * h) - φ (g * t)‖ * w ≤ |C₁| + |C₂|
    rcases le_or_gt 0 w with hw0 | hw0
    · calc ‖φ (g * t * h) - φ (g * t)‖ * w ≤ (‖φ (g * t * h)‖ + ‖φ (g * t)‖) * w :=
            mul_le_mul_of_nonneg_right (norm_sub_le _ _) hw0
        _ = ‖φ (g * t * h)‖ * w + ‖φ (g * t)‖ * w := by ring
        _ ≤ C₁ + C₂ := add_le_add e1 e2
        _ ≤ |C₁| + |C₂| := add_le_add (le_abs_self _) (le_abs_self _)
    · calc ‖φ (g * t * h) - φ (g * t)‖ * w ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hw0.le
        _ ≤ |C₁| + |C₂| := by positivity
  · intro hinv γ g
    simp only [mul_assoc]
    rw [hinv, hinv]
  · intro ω hω z g
    simp only [mul_assoc]
    rw [hω, hω, mul_sub]
  · exact key
  · intro pins ψ g hi1 hi2 hs1 hs2
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => ?_) (hs1.add hs2)
    rw [(key pins ψ α g (hi1 α) (hi2 α)).2]
    exact norm_sub_le _ _
  · intro pins ψ α β γ _ r f h' WA Wf hr hf hint hfac g
    rw [(key pins ψ α g (hint (g * h)) (hint g)).2, hfac, hfac, hr, hf]
    ring

end S_AutomorphicForm_continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate
end P2MW
export P2MW.S_AutomorphicForm_continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate (solution)
