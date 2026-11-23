-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_CompactIntegralBoundedByQuotientNorm
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_CompactIntegralBoundedByQuotientNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:32.846774+00:00
-- url     : https://prove2.me/theorems/0b2c2434-988d-4434-894d-249070a1ccde
-- title:
--   Compact Integral Bounded By Quotient Norm
-- statement:
--   Definitions and structural lemmas for Compact Integral Bounded By Quotient Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/CompactIntegralBoundedByQuotientNorm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Filter
open scoped ENNReal
noncomputable section
namespace CompanionTheory.D.gk.RF
section Defs
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
def LInv {α : Type} (Γ : Subgroup G) (f : G → α) : Prop := ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x
def Disc (Γ : Subgroup G) : Prop := ∀ C : Set G, IsCompact C → (C ∩ (Γ : Set G)).Finite
def BC (h : G → ℂ) : Prop := Continuous h ∧ ∃ M : ℝ, ∀ x, ‖h x‖ ≤ M
def IsRep (μ : Measure G) (φ : G → ℂ) (Γ : Subgroup G) (h : G → ℂ) : Prop :=
  BC h ∧ LInv Γ h ∧ ∀ x, h x = ∫ y, φ y * h (x * y) ∂μ
def CuspAt (μ : Measure G) (φ : G → ℂ) (Γ : Subgroup G) (O U : Set G) (x : G) : Prop :=
  ∃ ν : Measure G, IsProbabilityMeasure ν ∧ (∀ᵐ m ∂ν, x⁻¹ * m * x ∈ U) ∧
    ∀ h, IsRep μ φ Γ h → ∀ z ∈ O, ∫ m, h (m * x * z) ∂ν = 0
def sq (μ : Measure G) (D : Set G) (h : G → ℂ) : ℝ≥0∞ := ∫⁻ x in D, ‖h x‖ₑ ^ 2 ∂μ
def Detects (μ : Measure G) (φ : G → ℂ) (Γ : Subgroup G) (D : Set G) : Prop :=
  ∃ (m : ℕ) (α : G → ℂ) (p : Fin m → G), Continuous α ∧ HasCompactSupport α ∧
    ∀ h, IsRep μ φ Γ h → sq μ D h ≠ ∞ → (∀ i, ∫ y, α y * h (p i * y) ∂μ = 0) → sq μ D h = 0
structure ParData (N : Subgroup G) (a : ℝ → G) (Ht : G → ℝ) : Prop where
  cont : Continuous a
  add : ∀ s t, a (s + t) = a s * a t
  norm : ∀ t, ∀ m ∈ N, a t * m * (a t)⁻¹ ∈ N
  hcont : Continuous Ht
  hN : ∀ m ∈ N, ∀ g, Ht (m * g) = Ht g
  ha : ∀ t g, Ht (a t * g) = t + Ht g
  bd : ∃ c : G → ℝ, Continuous c ∧ ∀ x y, |Ht (x * y) - Ht x| ≤ c y
  small : ∀ U ∈ 𝓝 (1 : G), ∃ τ : ℝ, 0 < τ ∧ ∀ t, |t| < τ → ∀ x, ∃ m ∈ N, x⁻¹ * (m * a t) * x ∈ U
end Defs
def Young : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (D : Set G), IsFundamentalDomain Γ D μ →
    ∀ f θ : G → ℝ≥0∞, Measurable f → AEMeasurable θ μ → LInv Γ f →
      ∫⁻ x in D, (∫⁻ y, θ y * f (x * y) ∂μ) ^ 2 ∂μ ≤ (∫⁻ y, θ y ∂μ) ^ 2 * ∫⁻ x in D, f x ^ 2 ∂μ
def CompactIntegralBoundedByQuotientNorm : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (D : Set G), IsFundamentalDomain Γ D μ → Disc Γ →
    ∀ B : Set G, IsCompact B → ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ f : G → ℝ≥0∞, Measurable f → LInv Γ f →
      (∫⁻ y in B, f y ∂μ) ^ 2 ≤ M * ∫⁻ x in D, f x ^ 2 ∂μ
def NearMeas : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (D : Set G), IsFundamentalDomain Γ D μ →
    ∀ C : Set G, IsCompact C → MeasurableSet {x | ∃ γ ∈ Γ, γ * x ∈ C} ∧ μ (D ∩ {x | ∃ γ ∈ Γ, γ * x ∈ C}) ≤ μ C
def UnifC : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (α : G → ℂ), Continuous α → HasCompactSupport α → ∃ B : Set G, IsCompact B ∧ ∀ e : ℝ, 0 < e →
      ∃ U ∈ 𝓝 (1 : G), ∀ u ∈ U, ∀ y, ‖α (u⁻¹ * y) - α y‖ ≤ e ∧ (y ∉ B → α (u⁻¹ * y) = 0 ∧ α y = 0)
def Approx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (φ : G → ℂ) (O : Set G), Integrable φ μ → IsClopen O → (∀ y, y ∉ O → φ y = 0) → ∀ e : ℝ, 0 < e →
      ∃ α : G → ℂ, Continuous α ∧ HasCompactSupport α ∧ (∀ y, y ∉ O → α y = 0) ∧ ∫ y, ‖φ y - α y‖ ∂μ ≤ e
def FarEst : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (φ α : G → ℂ) (Γ : Subgroup G) (O U B : Set G) (e : ℝ), Continuous α → HasCompactSupport α →
    (∀ y, y ∉ O → α y = 0) → IsCompact B →
    (∀ u ∈ U, ∀ y, ‖α (u⁻¹ * y) - α y‖ ≤ e ∧ (y ∉ B → α (u⁻¹ * y) = 0 ∧ α y = 0)) →
    ∀ x, CuspAt μ φ Γ O U x → ∀ h, IsRep μ φ Γ h →
      ‖∫ y, α y * h (x * y) ∂μ‖ₑ ≤ ENNReal.ofReal e * ∫⁻ y in B, ‖h (x * y)‖ₑ ∂μ
def NearEst : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (D : Set G), IsFundamentalDomain Γ D μ → Disc Γ →
    ∀ α : G → ℂ, Continuous α → HasCompactSupport α → ∀ C : Set G, IsCompact C → ∀ e : ℝ≥0∞, 0 < e →
    ∃ (m : ℕ) (p : Fin m → G), ∀ h : G → ℂ, BC h → LInv Γ h → (∀ i, ∫ y, α y * h (p i * y) ∂μ = 0) →
      ∀ x ∈ C, ‖∫ y, α y * h (x * y) ∂μ‖ₑ ^ 2 ≤ e * sq μ D h
def Core : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (D : Set G), IsFundamentalDomain Γ D μ → Disc Γ →
    ∀ (φ : G → ℂ) (O : Set G), Integrable φ μ → IsClopen O → (∀ y, y ∉ O → φ y = 0) →
    (∀ U ∈ 𝓝 (1 : G), ∃ C : Set G, IsCompact C ∧ ∀ x, (∃ γ ∈ Γ, γ * x ∈ C) ∨ CuspAt μ φ Γ O U x) →
    Detects μ φ Γ D
def FiniteDimensionalFromLinearForms : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) (D : Set G) (φ : G → ℂ), Integrable φ μ → Detects μ φ Γ D →
    ∀ S : Submodule ℂ (Lp ℂ 2 (μ.restrict D)),
      (∀ F ∈ S, F ∈ closure {F' : Lp ℂ 2 (μ.restrict D) | ∃ h, IsRep μ φ Γ h ∧ (F' : G → ℂ) =ᵐ[μ.restrict D] h}) →
      FiniteDimensional ℂ S
def IdemZero : Prop :=
  ∀ (A : Type) [NormedRing A] (Q : ℝ → A), Continuous Q → (∀ s, Q s * Q s = Q s) → Tendsto Q atTop (𝓝 0) →
    ∀ s, Q s = 0
def SelTw : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (φ : G → ℂ), Integrable φ μ → (∀ w, ∫ y, φ y * φ (y⁻¹ * w) ∂μ = φ w) →
    ∀ (N : Subgroup G) (a : ℝ → G) (Ht : G → ℝ), ParData N a Ht →
    ∀ (s : ℝ) (F : G → ℂ), BC F → LInv N F → (∀ t x, F (a t * x) = F x) →
      ∀ x, ∫ y, φ y * (F (x * y) * Complex.exp (((s * Ht (x * y) : ℝ) : ℂ) * Complex.I)) ∂μ = 0
def Sel : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (φ : G → ℂ), Integrable φ μ → (∀ w, ∫ y, φ y * φ (y⁻¹ * w) ∂μ = φ w) →
    ∀ (N : Subgroup G) (a : ℝ → G) (Ht : G → ℝ), ParData N a Ht →
    ∀ F : G → ℂ, BC F → LInv N F → ∀ x, ∫ y, φ y * F (x * y) ∂μ = 0
def FundIn : Prop :=
  ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (Λ : Subgroup N), Disc Λ →
    ∀ V : Set N, IsOpen V → (∀ m, ∃ l ∈ Λ, l * m ∈ V) →
    ∃ D : Set N, MeasurableSet D ∧ D ⊆ V ∧ ∀ m, ∃! l : Λ, (l : N) * m ∈ D
def Avg : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Λ : Subgroup G),
    IsClosed (N : Set G) → Λ ≤ N → Disc Λ → ∀ V : Set G, IsOpen V → IsCompact (closure V) →
    (∀ m ∈ N, ∃ l ∈ Λ, l * m ∈ V) →
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ (∀ᵐ m ∂ν, m ∈ V) ∧
      ∀ u : G → ℂ, BC u → LInv Λ u → ∀ m₀ ∈ N, ∀ y, ∫ m, u (m * (m₀ * y)) ∂ν = ∫ m, u (m * y) ∂ν
end CompanionTheory.D.gk.RF


