-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_DiscreteSeriesTopClasses_IsMQEmpty
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_DiscreteSeriesTopClasses_IsMQEmpty
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:07.568422+00:00
-- url     : https://prove2.me/theorems/28fc9778-c30a-4631-9740-e8b5269f2e19
-- title:
--   Is MQEmpty
-- statement:
--   Definitions and structural lemmas for Is MQEmpty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/DiscreteSeriesTopClasses/IsMQEmpty.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix Filter Topology MeasureTheory
namespace PositivityTheory.RgTw
def prev {R : Type} [Zero R] (q : ℕ → R) : ℕ → R
  | 0 => 0
  | k + 1 => q k
def IsMQ {ι R : Type} [Fintype ι] [CommRing R] [Algebra ℂ R] (D : ι → Derivation ℂ R R) (s : ι → R) (P : ℕ → R)
    (Q : ι → ℕ → R) : Prop :=
  (∀ k : ℕ, (∑ a, s a ^ 2) * P k + (2 * (k : ℤ) + 2 - Fintype.card ι) • P (k + 1) =
      ∑ i, (D i (Q i k) + (∑ a, s a * D i (s a)) * prev (Q i) k)) ∧
    (∀ k, (2 * k < Fintype.card ι ∨ Fintype.card ι < k) → P k = 0) ∧
    ∀ i k, (2 * k + 1 < Fintype.card ι ∨ Fintype.card ι ≤ k) → Q i k = 0
def MQAlg : Prop :=
  ∀ (ι R : Type) [Fintype ι] [DecidableEq ι] [CommRing R] [Algebra ℂ R] (D : ι → Derivation ℂ R R) (s : ι → R)
    (r : ι → ι → Matrix ι ι ℂ), (∀ i j, (r i j)ᵀ = -r i j) → (∀ i j, r j i = -r i j) →
    (∀ i j a, D i (D j (s a)) - D j (D i (s a)) = ∑ b, r i j a b • s b) →
    ∃ P Q, IsMQ D s P Q ∧ P (Fintype.card ι) = (Matrix.of fun i a => D i (s a)).det
def BlowR : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (β : (ι → ℝ) → (ι → ℝ)) (L : (ι → ℝ) →L[ℝ] (ι → ℝ)),
    LinearMap.det (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) ≠ 0 → Continuous β → β 0 = 0 → HasFDerivAt β L 0 →
    (∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ B, ∑ x, β B x ^ 2 ≤ η → ‖B‖ ≤ δ) →
    ∀ F : ℝ → ℝ, Continuous F → (∀ x, 1 ≤ x → F x = 0) → ∀ ψ : (ι → ℝ) → ℂ, Continuous ψ →
      (∀ᶠ t : ℝ in atTop, Integrable fun B => (F (t ^ 2 * (∑ x, β B x ^ 2) / 2) : ℂ) * ψ B) ∧
      Tendsto (fun t : ℝ => (t : ℂ) ^ Fintype.card ι * ∫ B, (F (t ^ 2 * (∑ x, β B x ^ 2) / 2) : ℂ) * ψ B) atTop
        (𝓝 (ψ 0 * ((∫ w : ι → ℝ, F ((∑ x, w x ^ 2) / 2) : ℝ) : ℂ) /
          ((|LinearMap.det (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))| : ℝ) : ℂ)))
def Hopf : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (d T : Module.End ℂ V), d * d = 0 →
    T * d = -(d * T) → LinearMap.trace ℂ V T ≠ 0 → ∃ x, d x = 0 ∧ x ∉ LinearMap.range d
def DetAd : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), (∀ a, z a ≠ 0) →
    LinearMap.det ((LinearMap.id + (LinearMap.mulLeft ℂ (diagonal z)) ∘ₗ (LinearMap.mulRight ℂ (diagonal fun a => (z a)⁻¹)) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)) = ∏ a, ∏ b, (1 + z a / z b)
end PositivityTheory.RgTw


