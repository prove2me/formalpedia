-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:27.186244+00:00
-- url     : https://prove2.me/theorems/fb223231-45d4-490c-aea3-1c00791fb4fa
-- title:
--   Int Series
-- statement:
--   Definitions and structural lemmas for Int Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/IntSeries.lean

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
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries
noncomputable section
def IntSeriesConv (F : PowerSeries ℤ) (r : ℝ) : Prop :=
  Summable fun n ↦ |((coeff n F : ℤ) : ℝ)| * r ^ n
def intSeriesEval (F : PowerSeries ℤ) (z : ℂ) : ℂ :=
  ∑' n, ((coeff n F : ℤ) : ℂ) * z ^ n
end
end GroundTheory.Heights₂.Heights.ChowlaSelberg


