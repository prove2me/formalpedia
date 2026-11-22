-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:59.062703+00:00
-- url     : https://prove2.me/theorems/cd79373e-67fc-4512-ba6b-0156fa24a078
-- title:
--   Energy Abs
-- statement:
--   Definitions and structural lemmas for Energy Abs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/EnergyAbs.lean

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
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
set_option linter.dupNamespace false
namespace Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]
def rk1A {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] (v : V) (w : V') : V' →L[ℂ] V := (innerSL ℂ w).smulRight v
def hsA {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) : ℝ :=
  ∑ i, ‖A (stdOrthonormalBasis ℂ V' i)‖ ^ 2
def IsUnitRep [TopologicalSpace G] {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
    (σ : G → (HH →L[ℂ] HH)) : Prop :=
  σ 1 = 1 ∧ (∀ x y, σ (x * y) = σ x * σ y) ∧ (∀ x a b, ⟪σ x a, σ x b⟫_ℂ = ⟪a, b⟫_ℂ) ∧
    ∀ a, Continuous (fun x => σ x a)
def IsSchur {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] (μ : Measure G)
    (σ : G → (HH →L[ℂ] HH)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ a b a' b' : HH,
    Integrable (fun x => ⟪b, σ x a⟫_ℂ * conj ⟪b', σ x a'⟫_ℂ) μ ∧
      ∫ x, ⟪b, σ x a⟫_ℂ * conj ⟪b', σ x a'⟫_ℂ ∂μ = ⟪a', a⟫_ℂ * ⟪b, b'⟫_ℂ / (d : ℂ)
def IsHaarSub [TopologicalSpace G] (S : Set G) (μS : Measure G) : Prop :=
  IsClosed S ∧ (1 : G) ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ (∀ a ∈ S, a⁻¹ ∈ S) ∧
    SigmaFinite μS ∧ μS ≠ 0 ∧ μS Sᶜ = 0 ∧ (∀ s ∈ S, μS.map (fun x => s * x) = μS) ∧
    (∀ K : Set G, IsCompact K → μS K < ⊤) ∧ (∀ s ∈ S, μS.map (fun x => x * s) = μS) ∧ μS.map (fun x => x⁻¹) = μS
def IsFolner (S : Set G) (μS : Measure G) [TopologicalSpace G] : Prop :=
  ∀ K : Set G, IsCompact K → K ⊆ S → ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ Ω : Set G, MeasurableSet Ω ∧ Ω ⊆ S ∧ 0 < μS Ω ∧ μS Ω < ⊤ ∧
      μS Ω ≤ (1 + ε) * μS {t | t ∈ Ω ∧ ∀ k ∈ K, k * t ∈ Ω}
def IsQuot (μ μS ν : Measure G) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν
def IsWAbs [TopologicalSpace G] {HH V : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (μ : Measure G) (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH)
    (S : Set G) (τ : G → (V →L[ℂ] V)) (ν : Measure G) (W : G → V) : Prop :=
  τ 1 = 1 ∧ (∀ s ∈ S, ∀ t ∈ S, τ (s * t) = τ s * τ t) ∧ (∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ) ∧
    (∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) ∧ Continuous W ∧
    (∀ x, Integrable (fun y => ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (x * y)) μ ∧
      ∫ y, ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (x * y) ∂μ = W x) ∧
    ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤ ∧ ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν = 1
def IsDisint {C : Type} [MeasurableSpace C] (μ μS μS' : Measure G) (m : Measure C) (h : C → G) : Prop :=
  ∀ φ : G → ℝ≥0∞, Measurable φ →
    ∫⁻ x, φ x ∂μ = ∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * h c * s'⁻¹) ∂μS' ∂μS ∂m
def EnergyAbs : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (HH : Type) [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
    (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH)
    (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (S S' : Set G) (μS μS' ν ν' : Measure G) (τ : G → (V →L[ℂ] V)) (τ' : G → (V' →L[ℂ] V'))
    (W : G → V) (W' : G → V') (C : Type) (_ : MeasurableSpace C) (m : Measure C) (h : C → G),
    IsUnitRep σ → IsSchur μ σ d → ‖w‖ = 1 →
    IsHaarSub S μS → IsHaarSub S' μS' → IsFolner S μS → IsFolner S' μS' →
    SFinite ν → SFinite ν' → IsQuot μ μS ν → IsQuot μ μS' ν' →
    IsWAbs μ σ d w S τ ν W → IsWAbs μ σ d w S' τ' ν' W' →
    IsDisint μ μS μS' m h → Measurable h →
    (∀ c, Integrable (fun x => rk1A (W x) (W' ((h c)⁻¹ * x))) μ) →
    (∀ c, ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪σ z w, σ (s * h c * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ
      ∂μS' ∂μS ∂ν' ∂ν < ⊤) →
    (∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤) →
    (∫⁻ z, ∫⁻ z', ∫⁻ s', ‖⟪σ z w, σ s' (σ z' w)⟫_ℂ‖ₑ * ‖W' z‖ₑ * ‖W' z'‖ₑ ∂μS' ∂ν' ∂ν' < ⊤) →
    ∫⁻ c, ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' ((h c)⁻¹ * x)) ∂μ)) ∂m ≤ ENNReal.ofReal (1 / d)
end Formalism.L2.SG.Pf.EnergyAbs


