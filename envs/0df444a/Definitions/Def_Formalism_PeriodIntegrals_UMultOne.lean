-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UMultOne
-- name    : Formalism_PeriodIntegrals_UMultOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:40.791988+00:00
-- url     : https://prove2.me/theorems/73966c54-3a03-413a-8fe4-625a92d7028d
-- title:
--   UMult One
-- statement:
--   Definitions and structural lemmas for UMult One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UMultOne.lean

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
namespace PI.UMultOne
open MeasureTheory Matrix ComplexConjugate Finset
def MultOne : Prop :=
  ∀ (n N M : ℕ) (ι : Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin (n + 1)) ℂ),
    (∀ g, ((ι g : Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))) →
    ∀ (ρ : Matrix.unitaryGroup (Fin (n + 1)) ℂ →* GL (Fin N) ℂ)
      (σ : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin M) ℂ),
    Continuous (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) →
    Continuous (fun g => ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
    0 < N → 0 < M →
    (∀ S : Submodule ℂ (Fin N → ℂ),
      (∀ g, ∀ v ∈ S, ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).mulVec v ∈ S) →
      S = ⊥ ∨ S = ⊤) →
    (∀ S : Submodule ℂ (Fin M → ℂ),
      (∀ g, ∀ v ∈ S, ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ).mulVec v ∈ S) →
      S = ⊥ ∨ S = ⊤) →
    ∀ Hm : Submodule ℂ (Matrix (Fin N) (Fin M) ℂ),
      (∀ T, T ∈ Hm ↔ ∀ g, ((ρ (ι g) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T =
        T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
      Module.finrank ℂ Hm ≤ 1
def blk (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks h 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))
def ConjTranspose : Prop :=
  ∀ (n : ℕ) (g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), g ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ →
    ∃ h ∈ Matrix.unitaryGroup (Fin n) ℂ, blk n h * g * (blk n h)ᴴ = gᵀ
def Irr {G : Type} [Group G] {N : ℕ} (ρ : G →* GL (Fin N) ℂ) : Prop :=
  ∀ S : Submodule ℂ (Fin N → ℂ),
    (∀ g, ∀ v ∈ S, ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤
def Cont {G : Type} [Group G] [TopologicalSpace G] {N : ℕ} (ρ : G →* GL (Fin N) ℂ) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))
def GelfandCompact : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] (H : Subgroup G) (τ : G → G), IsClosed (H : Set G) → Continuous τ →
    (∀ x y, τ (x * y) = τ y * τ x) → (∀ x, τ (τ x) = x) → (∀ g, ∃ h ∈ H, τ g = h * g * h⁻¹) →
    ∀ (N : ℕ) (ρ : G →* GL (Fin N) ℂ), Cont ρ → Irr ρ →
    ∀ A B : Matrix (Fin N) (Fin N) ℂ,
      (∀ h ∈ H, ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * A = A * ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) →
      (∀ h ∈ H, ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * B = B * ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) → A * B = B * A
def IntSpan : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (N : ℕ) (ρ : G →* GL (Fin N) ℂ), Cont ρ → Irr ρ →
    ∀ T : Matrix (Fin N) (Fin N) ℂ, ∃ f : G → ℂ, Continuous f ∧
      ∀ i j, T i j = ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ
def ConvComm : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (τ : G → G), Continuous τ →
    (∀ x y, τ (x * y) = τ y * τ x) → (∀ x, τ (τ x) = x) → (∀ g, ∃ h ∈ H, τ g = h * g * h⁻¹) →
    ∀ f₁ f₂ : G → ℂ, Continuous f₁ → Continuous f₂ →
      (∀ h ∈ H, ∀ x, f₁ (h * x * h⁻¹) = f₁ x) → (∀ h ∈ H, ∀ x, f₂ (h * x * h⁻¹) = f₂ x) →
      ∀ z, ∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ = ∫ x, f₂ x * f₁ (x⁻¹ * z) ∂μ
def CommutantMult : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
    [SecondCountableTopology H] (N M : ℕ) (π : H →* GL (Fin N) ℂ) (σ : H →* GL (Fin M) ℂ),
    Cont π → Cont σ → Irr σ →
    (∀ A B : Matrix (Fin N) (Fin N) ℂ,
      (∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * A = A * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) →
      (∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * B = B * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) → A * B = B * A) →
    ∀ Hm : Submodule ℂ (Matrix (Fin N) (Fin M) ℂ),
      (∀ T, T ∈ Hm ↔ ∀ g, ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T = T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
      Module.finrank ℂ Hm ≤ 1
end PI.UMultOne


