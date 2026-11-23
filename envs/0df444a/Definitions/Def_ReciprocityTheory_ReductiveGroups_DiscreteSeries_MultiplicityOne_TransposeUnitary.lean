-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_TransposeUnitary
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_TransposeUnitary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:41:33.791648+00:00
-- url     : https://prove2.me/theorems/2466dbd8-0b19-4448-b101-6a701c9f2a79
-- title:
--   Transpose Unitary
-- statement:
--   Definitions and structural lemmas for Transpose Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/TransposeUnitary.lean

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
open MeasureTheory
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.Mult1
def RankOneMinors : Prop :=
  ∀ (X : Type) (κ : X → X → ℂ),
    (∀ x y, κ x y = star (κ y x)) → (∀ x, 0 ≤ (κ x x).re) →
    (∀ x y x' y', κ x y * κ x' y' = κ x y' * κ x' y) →
    ∃ f : X → ℂ, ∀ x y, κ x y = f x * star (f y)
def TransposeUnitary : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (c : E ≃ₗᵢ⋆[ℂ] E) (w₁ : E) (y : E ≃ₗᵢ[ℂ] E),
    (∀ v, c (c v) = v) → c w₁ = w₁ →
    ∃ u₀ : E ≃ₗᵢ[ℂ] E, u₀ w₁ = w₁ ∧ ∀ v, u₀ (y (u₀.symm v)) = c (y.symm (c v))
def SchurDichotomy : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant] [μ.IsOpenPosMeasure]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (θ : G → G) (ρ : G → (H →L[ℂ] H)),
    Continuous θ → (∀ a b, θ (a * b) = θ b * θ a) → (∀ g, θ (θ g) = g) → μ.map θ = μ →
    ρ 1 = 1 → (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) → (∀ g v, ‖ρ g v‖ = ‖v‖) →
    (∀ v, Continuous fun g => ρ g v) → (∀ v w, MemLp (fun g => ⟪w, ρ g v⟫_ℂ) 2 μ) →
    (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤) →
    (∀ x y x' y' : H, ∫ g, ⟪y, ρ (θ g) x⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ ∂μ = 0) ∨
    ∃ C : H ≃ₗᵢ⋆[ℂ] H, (∀ g (x y : H), ⟪y, ρ (θ g) x⟫_ℂ = ⟪C x, ρ g (C y)⟫_ℂ) ∧
      ∀ h (v : H), C (ρ h v) = ρ (θ h)⁻¹ (C v)
end ReciprocityTheory.ChartRestriction.DS.Mult1


