-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianLogGrowth
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianLogGrowth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:39.661624+00:00
-- url     : https://prove2.me/theorems/2b2c3993-2b54-47c0-997b-bb8a3e68c42e
-- title:
--   Statements Laplacian Log Growth
-- statement:
--   Definitions and structural lemmas for Statements Laplacian Log Growth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/StatementsLaplacianLogGrowth.lean

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian Real
def LaplacianLogGrowth.Statement : Prop :=
  ∀ (u F : ℂ → ℝ) (a r : ℝ), ContDiff ℝ 2 u → 0 < r → ContDiffOn ℝ 2 F (Metric.ball 0 r) →
    (∀ y : ℂ, r⁻¹ < ‖y‖ → u y = a * Real.log ‖y‖ + F y⁻¹) →
    MeasureTheory.Integrable (Δ u) ∧ ∫ y, Δ u y = 2 * π * a
def fsPotPlane (y : ℂ) : ℝ := Real.log (1 + ‖y‖ ^ 2) / 2
end GroundTheory.Heights₂.Heights.LowerBoundFree


