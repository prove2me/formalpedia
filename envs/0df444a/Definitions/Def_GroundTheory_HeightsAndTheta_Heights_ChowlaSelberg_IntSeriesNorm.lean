-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesNorm
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:07.383246+00:00
-- url     : https://prove2.me/theorems/53695cf2-bd31-4739-93a8-3a67d4e72982
-- title:
--   Int Series Norm
-- statement:
--   Definitions and structural lemmas for Int Series Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/IntSeriesNorm.lean

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
def IntSeriesNorm.Statement : Prop :=
  ∀ (F : PowerSeries ℤ) (r : ℝ), 0 < r → IntSeriesConv F r → ∀ p : ℕ, 0 < p → ∀ j : ℕ,
    ∃ E : PowerSeries ℤ, IntSeriesConv E (r ^ p) ∧ ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ r →
      ((Multiset.range p).map fun a : ℕ ↦
          intSeriesEval F (Complex.exp (2 * π * Complex.I * a / p) * t)).esymm j =
        intSeriesEval E (t ^ p)
end
end GroundTheory.Heights₂.Heights.ChowlaSelberg


