-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:04.417399+00:00
-- url     : https://prove2.me/theorems/64d08e39-a7f4-4334-b12c-21898e0dec99
-- title:
--   Qmu Weight
-- statement:
--   Definitions and structural lemmas for Qmu Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QmuWeight.lean

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
open scoped ENNReal
namespace PI.QuotMeasUniqW
def QmuWeight : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ν : Measure H, ν.IsHaarMeasure →
      ∃ w : G → ℝ≥0∞, Measurable w ∧
        ∀ g : G, (∫⁻ h, w (g * (h : G)) ∂ν) ≠ 0 ∧ (∫⁻ h, w (g * (h : G)) ∂ν) ≠ ⊤
def QmuLift : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ν : Measure H, ν.IsHaarMeasure →
    ∀ ρ : Measure (G ⧸ H), (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) →
      ∃ l : Measure G, l.IsMulLeftInvariant ∧ IsFiniteMeasureOnCompacts l ∧
        ∀ f : G → ℝ≥0∞, Measurable f →
          ∫⁻ x, f x ∂l = ∫⁻ y, (∫⁻ h, f (y.out * (h : G)) ∂ν) ∂ρ
end PI.QuotMeasUniqW


