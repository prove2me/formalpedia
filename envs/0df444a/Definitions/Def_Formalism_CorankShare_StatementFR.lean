-- Prove2me | Definitions.Def_Formalism_CorankShare_StatementFR
-- name    : Formalism_CorankShare_StatementFR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:14.797154+00:00
-- url     : https://prove2.me/theorems/9187a325-c84c-454a-94a3-75b7fd131474
-- title:
--   Statement FR
-- statement:
--   Definitions and structural lemmas for Statement FR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/StatementFR.lean

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
namespace Formalism.CorankShareLayerCake.FR
open Finset Module LinearMap
def hs2 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (A : E →ₗ[ℂ] F) : ℝ :=
  (LinearMap.trace ℂ E (LinearMap.adjoint A ∘ₗ A)).re
def frK {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (c : ℝ) (B : V →ₗ[ℂ] H) : V →ₗ[ℂ] V :=
  (c : ℂ) • (LinearMap.adjoint B ∘ₗ B)
def frQ {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  ∑ i, (c i : ℂ) • (B i ∘ₗ LinearMap.adjoint (B i))
def CorankShare : Prop :=
  ∀ (R : ℕ) (x : Fin R → ℝ) (s u τ : ℝ), 0 < u → 0 ≤ τ →
    (R : ℝ) * s ≤ ∑ j, x j → (∀ j, x j ≤ s + u) →
    ((univ.filter (fun j => x j < s - τ)).card : ℝ) ≤ R * (u / (u + τ))
def FrameLA : Prop :=
  ∀ (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (B : ∀ i, V i →ₗ[ℂ] H) (c : ι → ℝ) (Nτ : ∀ i, Submodule ℂ (V i)) (e η ε : ℝ),
    (∀ i, 0 < c i) →
    0 < ∑ i, finrank ℂ (V i) →

    (∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ e * ∑ i, (finrank ℂ (V i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →

    (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re
      ≤ (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) →

    (∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i))) ≤ ε * ∑ i, (finrank ℂ (V i) : ℝ) →
    (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ)
      ≤ (2 * η + 4 * ε + 4 * Real.sqrt e) * (finrank ℂ H : ℝ)
def LayerCake : Prop :=
  ∀ (D : ℕ) (x : Fin D → ℝ) (a HH : ℝ) (w : ℝ → ℝ), 0 < D → 0 ≤ HH →
    (∀ j, a - HH ≤ x j) →
    IntervalIntegrable (fun τ => min 1 (w τ)) MeasureTheory.volume 0 HH →
    (∀ τ ∈ Set.Icc (0 : ℝ) HH, ((univ.filter (fun j => x j < a - τ)).card : ℝ) ≤ w τ * D) →
    a - (∫ τ in (0 : ℝ)..HH, min 1 (w τ)) ≤ (∑ j, x j) / D
def FrameLast : Prop :=
  ∀ (D : ℕ) (x : Fin D → ℝ) (s h L u HH η e : ℝ), 0 < D → 0 ≤ L → 0 < u → 0 ≤ HH →
    0 ≤ η → 0 ≤ e →
    (∀ j, s - h - HH ≤ x j) →
    (∀ τ ∈ Set.Icc (0 : ℝ) HH, ((univ.filter (fun j => x j < s - τ - h - L)).card : ℝ)
        ≤ (2 * η + 4 * (u / (u + τ)) + 4 * Real.sqrt e) * D) →
    s - h - L - u * (1 + 8 * Real.log (1 + HH / u)) - (4 * η + 8 * Real.sqrt e) * HH
      ≤ (∑ j, x j) / D
end Formalism.CorankShareLayerCake.FR


