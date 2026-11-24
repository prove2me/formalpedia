-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRemovableHyperplane
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRemovableHyperplane
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:52.516393+00:00
-- url     : https://prove2.me/theorems/f0785c7c-2111-4196-9cf0-b4263db3844e
-- title:
--   St Removable Hyperplane
-- statement:
--   Definitions and structural lemmas for St Removable Hyperplane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRemovableHyperplane.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
noncomputable section
def RemovableHyperplane.Statement : Prop :=
  ∀ (k n : ℕ) (R : ℝ) (f : (Fin (k + 1) → ℂ) → Fin n → ℂ),
    DifferentiableOn ℂ f (Metric.ball 0 R ∩ {t | t 0 ≠ 0}) →
    Bornology.IsBounded (f '' (Metric.ball 0 R ∩ {t | t 0 ≠ 0})) →
    ∃ g : (Fin (k + 1) → ℂ) → Fin n → ℂ, DifferentiableOn ℂ g (Metric.ball 0 R) ∧
      Set.EqOn g f (Metric.ball 0 R ∩ {t | t 0 ≠ 0})
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


