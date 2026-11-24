-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNonIsolatedFibreCurve
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNonIsolatedFibreCurve
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:37.540523+00:00
-- url     : https://prove2.me/theorems/352def83-9123-4b13-b31f-af35e725ea96
-- title:
--   St Non Isolated Fibre Curve
-- statement:
--   Definitions and structural lemmas for St Non Isolated Fibre Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNonIsolatedFibreCurve.lean

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
open Topology Metric Filter
def NonIsolatedFibreCurve.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ) (p : Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → p ∈ U → AccPt p (𝓟 {v | v ∈ U ∧ f v = f p}) →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → Fin k → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = p ∧
          Set.MapsTo γ (ball 0 r) {v | v ∈ U ∧ f v = f p}
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


