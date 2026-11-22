-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLattice
-- name    : Formalism_FlagUnipotentLattices_FlagUnipotentLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:01.332651+00:00
-- url     : https://prove2.me/theorems/80167ca6-fad2-4827-8a1c-32459e871cca
-- title:
--   Flag Unipotent Lattice
-- statement:
--   Definitions and structural lemmas for Flag Unipotent Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/FlagUnipotentLattice.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField Matrix
noncomputable section
namespace Formalism.HermitianLatticeCounting.S7
def KernelZeroEquiv : Prop :=
  ∀ (K H L : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (act : K → L → K) (ρ : L → H →L[ℂ] H)
    (κ : K → H →L[ℂ] H), Continuous κ → (∀ k l, κ (act k l) = κ k ∘L ρ l) →
    (∀ φ : K → H, Continuous φ → (∀ k l, φ (act k l) = ContinuousLinearMap.adjoint (ρ l) (φ k)) →
      (∫ k, κ k (φ k) ∂μ) = 0) → ∀ k, κ k = 0
def KernelZeroUnitary : Prop :=
  ∀ (K H L : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (act : K → L → K) (ρ : L → H ≃ₗᵢ[ℂ] H)
    (κ : K → H →L[ℂ] H), Continuous κ → (∀ k l v, κ (act k l) v = κ k (ρ l v)) →
    (∀ φ : K → H, Continuous φ → (∀ k l, φ (act k l) = (ρ l).symm (φ k)) →
      (∫ k, κ k (φ k) ∂μ) = 0) → ∀ k, κ k = 0
def ResidueRingCard : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g : ℕ),
    Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) = g ^ Module.finrank ℚ E
def LevelIndexField : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g n : ℕ), 1 ≤ g →
    Nat.card (Matrix (Fin n) (Fin n) (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}))ˣ ≤ (g ^ Module.finrank ℚ E) ^ (n ^ 2)
def FlagUnipotent : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (m : ℕ) (F : ℕ → Submodule R V)
    (γ : V →ₗ[R] V), F 0 = ⊥ → F m = ⊤ → (∀ i < m, ∀ x ∈ F (i + 1), γ x - x ∈ F i) → (γ - 1) ^ m = 0
def FlagUnipotentRel : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (m : ℕ) (F : ℕ → Submodule R V)
    (γ : V →ₗ[R] V), (∀ i < m, ∀ x ∈ F (i + 1), γ x - x ∈ F i) → ∀ x ∈ F m, ((γ - 1) ^ m) x ∈ F 0
def FlagUnipotentLattice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (γ : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (P : Ideal (𝓞 E)) (F : ℕ → Submodule (𝓞 E) (Fin n → E)),
    F 0 = P • L → F n = L → (∀ i < n, ∀ x ∈ F (i + 1), γ *ᵥ x - x ∈ F i) →
    ∀ x ∈ L, ((γ - 1) ^ n) *ᵥ x ∈ P • L
end Formalism.HermitianLatticeCounting.S7


