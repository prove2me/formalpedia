-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermCurve
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermCurve
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:55.374506+00:00
-- url     : https://prove2.me/theorems/f94b431f-f695-406c-99f9-bbb3fe24ba25
-- title:
--   St Irreducible Germ Curve
-- statement:
--   Definitions and structural lemmas for St Irreducible Germ Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StIrreducibleGermCurve.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
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
def IrreducibleGermCurve.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ),
    IsAnalyticNear X w → GermIrreducibleAt X w → AccPt w (𝓟 X) →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) X
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


