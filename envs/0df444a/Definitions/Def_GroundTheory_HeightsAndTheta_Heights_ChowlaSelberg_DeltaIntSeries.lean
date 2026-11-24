-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:58.28517+00:00
-- url     : https://prove2.me/theorems/f054a8e6-6b13-454b-ba3d-177614b62720
-- title:
--   Delta Int Series
-- statement:
--   Definitions and structural lemmas for Delta Int Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/DeltaIntSeries.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries
open scoped Real
noncomputable section
def DeltaIntSeries.Statement : Prop :=
  ∃ D : PowerSeries ℤ, coeff 0 D = 1 ∧ (∀ r : ℝ, 0 ≤ r → r < 1 → IntSeriesConv D r) ∧
    ∀ τ : UpperHalfPlane, ModularForm.discriminant τ =
      Function.Periodic.qParam 1 τ * intSeriesEval D (Function.Periodic.qParam 1 τ)
end
end GroundTheory.Heights₂.Heights.ChowlaSelberg


