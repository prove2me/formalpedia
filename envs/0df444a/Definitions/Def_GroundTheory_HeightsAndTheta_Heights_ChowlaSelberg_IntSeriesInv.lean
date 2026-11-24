-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesInv
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:41.249778+00:00
-- url     : https://prove2.me/theorems/4dddab78-f5e0-46ee-8791-4a11deb465a8
-- title:
--   Int Series Inv
-- statement:
--   Definitions and structural lemmas for Int Series Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/IntSeriesInv.lean

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
def IntSeriesInv.Statement : Prop :=
  ∀ (F : PowerSeries ℤ) (r : ℝ), 0 < r → IntSeriesConv F r → coeff 0 F = 1 →
    ∃ (G : PowerSeries ℤ) (r' : ℝ), 0 < r' ∧ IntSeriesConv G r' ∧ F * G = 1
end
end GroundTheory.Heights₂.Heights.ChowlaSelberg


