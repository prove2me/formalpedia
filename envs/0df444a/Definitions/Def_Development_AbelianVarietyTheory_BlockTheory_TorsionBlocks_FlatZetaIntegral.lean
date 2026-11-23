-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_FlatZetaIntegral
-- name    : Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_FlatZetaIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:24.481924+00:00
-- url     : https://prove2.me/theorems/923d682f-c236-4846-a947-b5c9787b7862
-- title:
--   Flat Zeta Integral
-- statement:
--   Definitions and structural lemmas for Flat Zeta Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/FlatZetaIntegral.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
variable {X : Type} [MeasurableSpace X]
noncomputable def flatIntegrand (f : X → ℂ) (a : X → ℝ) (s₀ s : ℂ) (x : X) : ℂ :=
  f x * ((a x : ℝ) : ℂ) ^ (s - s₀)
noncomputable def flatZeta (μ : Measure X) (f : X → ℂ) (a : X → ℝ) (s₀ s : ℂ) : ℂ :=
  ∫ x, flatIntegrand f a s₀ s x ∂μ
def ConvergesAbsLocUnifOn (μ : Measure X) (F : ℂ → X → ℂ) (D : Set ℂ) : Prop :=
  (∀ s ∈ D, Integrable (F s) μ) ∧
    ∀ s ∈ D, ∃ U ∈ nhdsWithin s D, ∃ g : X → ℝ, Integrable g μ ∧
      ∀ s' ∈ U, ∀ x, ‖F s' x‖ ≤ g x
def FlatZetaHolomorphic : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : X → ℂ) (a : X → ℝ) (s₀ s₁ : ℂ),
    Measurable a → (∀ x, 0 < a x) → (∀ x, a x ≤ 1) →
    Integrable (flatIntegrand f a s₀ s₁) μ →
      ConvergesAbsLocUnifOn μ (flatIntegrand f a s₀) {s | s₁.re ≤ s.re} ∧
      DifferentiableOn ℂ (flatZeta μ f a s₀) {s | s₁.re < s.re} ∧
      ContinuousOn (flatZeta μ f a s₀) {s | s₁.re ≤ s.re}
example (s : ℂ) :
    Integrable (flatIntegrand (fun _ : Unit => (1 : ℂ)) (fun _ => (1 / 2 : ℝ)) 0 s)
        (Measure.dirac ()) ∧
      flatZeta (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => (1 / 2 : ℝ)) 0 s
        = (((1 / 2 : ℝ) : ℝ) : ℂ) ^ s := by
  refine ⟨?_, ?_⟩
  · exact Integrable.of_finite
  · simp [flatZeta, flatIntegrand]
end GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral


