-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:42.523345+00:00
-- url     : https://prove2.me/theorems/be983086-b023-4d1a-b42d-461e456e4ba8
-- title:
--   St Parametric Circle Integral Analytic
-- statement:
--   Definitions and structural lemmas for St Parametric Circle Integral Analytic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StParametricCircleIntegralAnalytic.lean

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
open Topology Filter Metric
noncomputable section
def ParametricCircleIntegralAnalytic.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Φ : (ι → ℂ) × ℂ → ℂ) (O : Set ((ι → ℂ) × ℂ)) (U : Set (ι → ℂ)) (c : ℂ) (r : ℝ),
    0 ≤ r → IsOpen O → IsOpen U → DifferentiableOn ℂ Φ O →
    (∀ x ∈ U, ∀ s ∈ sphere c r, (x, s) ∈ O) →
    AnalyticOnNhd ℂ (fun x => ∮ s in C(c, r), Φ (x, s)) U
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


