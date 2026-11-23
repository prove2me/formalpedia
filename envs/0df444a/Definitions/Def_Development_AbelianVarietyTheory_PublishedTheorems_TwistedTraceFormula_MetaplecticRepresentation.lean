-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:22.534124+00:00
-- url     : https://prove2.me/theorems/65fddd7d-560c-43e2-b824-efe408a2690f
-- title:
--   Metaplectic Representation
-- statement:
--   Definitions and structural lemmas for Metaplectic Representation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/MetaplecticRepresentation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
namespace GlobalTheory.Published
namespace Metaplectic
variable {ι : Type} [Fintype ι]
def eChar : AddChar ℝ ℂ := Circle.coeHom.compAddChar Real.fourierChar
def rho (w : (ι → ℝ) × (ι → ℝ)) : 𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x => eChar (x ⬝ᵥ w.2 + ⅟(2 : ℝ) * (w.1 ⬝ᵥ w.2))) ∘L
    SchwartzMap.compSubConstCLM ℂ (-w.1)
def act (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (w : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  ((g *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (g *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)
def holPart (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) : Matrix ι ι ℂ := fun i j =>
  ((g (.inl i) (.inl j) + g (.inr i) (.inr j) : ℝ) + I * (g (.inr i) (.inl j) - g (.inl i) (.inr j) : ℝ)) / 2
end Metaplectic
open Metaplectic
def MetaplecticRepresentation : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (pr : G →* symplecticGroup ι ℝ)
      (Ω : G →* (Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))))
      (ω : G →* (𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ))) (φ₀ : 𝓢(ι → ℝ, ℂ)),
      Function.Surjective pr ∧ IsCoveringMap pr ∧ Nat.card pr.ker = 2 ∧
      (∀ g f, ‖Ω g f‖ = ‖f‖) ∧ (∀ f, Continuous fun g => Ω g f) ∧
      (∀ g (φ : 𝓢(ι → ℝ, ℂ)), Ω g (φ.toLp 2) = (ω g φ).toLp 2) ∧
      (Continuous fun x : G × 𝓢(ι → ℝ, ℂ) => ω x.1 x.2) ∧
      (∀ g w φ, ω g (rho w φ) = rho (act (pr g).1 w) (ω g φ)) ∧
      (∀ g, pr g = 1 → g ≠ 1 → ∀ φ, ω g φ = -φ) ∧
      (∀ x, φ₀ x = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))) ∧
      (∀ g, (∫ x, ω g φ₀ x * conj (φ₀ x)) ^ 2 * (holPart (pr g).1).det = (∫ x, φ₀ x * conj (φ₀ x)) ^ 2) ∧
      (∀ g, (pr g).1ᵀ * (pr g).1 = 1 → ∃ c : ℂ, c ^ 2 * (holPart (pr g).1).det = 1 ∧ ω g φ₀ = c • φ₀)
end GlobalTheory.Published
end


