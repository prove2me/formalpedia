-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
-- name    : Formalism_PeriodIntegrals_WeilQuotMeas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:05.7433+00:00
-- url     : https://prove2.me/theorems/fe2cce6b-60e2-4ce8-9c86-9f86cc0682da
-- title:
--   Weil Quot Meas
-- statement:
--   Definitions and structural lemmas for Weil Quot Meas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/WeilQuotMeas.lean

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
open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix
namespace PI.WeilQuotMeas
def WeilQuotient : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μ : Measure G) (ν : Measure H), μ.IsHaarMeasure → μ.IsMulRightInvariant → ν.IsHaarMeasure →
      ν.IsMulRightInvariant →
      ∃ ρ : Measure (G ⧸ H), ρ ≠ 0 ∧ (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) ∧
        (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) ∧
        (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ y, (∫⁻ h, f (y.out * h) ∂ν) ∂ρ) ∧
        ∀ ρ' : Measure (G ⧸ H), (∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) →
          (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s) →
          ∃ c : ℝ≥0∞, ρ' = c • ρ
def WqAvgOnto : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ν : Measure H, ν.IsHaarMeasure →
      ∀ φ : G ⧸ H → ℝ, Continuous φ → HasCompactSupport φ →
        ∃ f : G → ℝ, Continuous f ∧ HasCompactSupport f ∧
          ∀ g : G, ∫ h, f (g * (h : G)) ∂ν = φ (g : G ⧸ H)
def WqUnique : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ρ ρ' : Measure (G ⧸ H), ρ ≠ 0 →
      (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) →
      (∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s) →
      ∃ c : ℝ≥0∞, ρ' = c • ρ
end PI.WeilQuotMeas


