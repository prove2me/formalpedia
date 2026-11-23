-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_StepBruhat
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_StepBruhat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:15.716276+00:00
-- url     : https://prove2.me/theorems/a330ad95-339d-41b9-9f53-82e6c3970177
-- title:
--   Step Bruhat
-- statement:
--   Definitions and structural lemmas for Step Bruhat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientMeasure/StepBruhat.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
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
namespace PI.WeilQuotMeas.UnitaryGroupMassFormula
def StepBruhat : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ν : Measure H, ν.IsHaarMeasure →
      ∃ β : G → ℝ≥0∞, Measurable β ∧ ∀ g : G, ∫⁻ h, β (g * (h : G)) ∂ν = 1
def StepInvInv : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K),
    ν.IsHaarMeasure → ν.IsMulRightInvariant → ν.IsInvInvariant
end PI.WeilQuotMeas.UnitaryGroupMassFormula


