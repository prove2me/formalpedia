-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_CosDens
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_CosDens
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:40.030612+00:00
-- url     : https://prove2.me/theorems/26539401-b649-4fe9-ad87-0b9f57fd77b1
-- title:
--   Cos Dens
-- statement:
--   Definitions and structural lemmas for Cos Dens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/CosDens.lean

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
namespace PI.VolStabSW
open MeasureTheory Topology
def CosDens : Prop :=
  ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (ν m : Measure X) [IsFiniteMeasure m],
    IsFiniteMeasureOnCompacts ν →
    ∀ (H : ℕ → AddSubgroup X), (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      Antitone H → (∀ N ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N) →
      ∀ (c0 : X) (κ : ENNReal), m {z | z - c0 ∈ H 0}ᶜ = 0 →
        (∀ n h, h - c0 ∈ H 0 → m {z | z - h ∈ H n} = κ * ν {z | z - h ∈ H n}) →
        ∀ S : Set X, IsCompact S → m S = κ * ν (S ∩ {z | z - c0 ∈ H 0})
end PI.VolStabSW


