-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HenselCount
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HenselCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:42.453362+00:00
-- url     : https://prove2.me/theorems/8faa8958-0e45-4867-997f-c8372781752a
-- title:
--   Hensel Count
-- statement:
--   Definitions and structural lemmas for Hensel Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/HenselCount.lean

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
namespace PI.VolStabW
open MeasureTheory Topology
def HenselCount : Prop :=
  ∀ (V X : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), (∀ n, IsOpen (Λ n : Set V)) →
      (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ → (∀ n, IsOpen (H n : Set X)) →
      (∀ n, IsCompact (H n : Set X)) →
      ∀ D : V →+ X, (∀ n, (Λ n).map D = H n) →
      ∀ (G : V → X) (y : V),
        (∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
        ∀ n h, h - G y ∈ H 0 →
          μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} * ν (H 0) = μ (Λ 0) * ν (H n)
end PI.VolStabW


