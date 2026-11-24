-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:50.257383+00:00
-- url     : https://prove2.me/theorems/2d9444e0-3155-45ed-9a73-62fed7831cc0
-- title:
--   Int Series Ring
-- statement:
--   Definitions and structural lemmas for Int Series Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/IntSeriesRing.lean

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
def IntSeriesRing.Statement : Prop :=
  ∀ r : ℝ, 0 ≤ r →
    (∃ S : Subring (PowerSeries ℤ), ∀ F, F ∈ S ↔ IntSeriesConv F r) ∧
    (∀ F G, IntSeriesConv F r → IntSeriesConv G r → ∀ z : ℂ, ‖z‖ ≤ r →
      intSeriesEval (F * G) z = intSeriesEval F z * intSeriesEval G z) ∧
    (∀ F, IntSeriesConv F r → ∀ z : ℂ, ‖z‖ ≤ r →
      HasSum (fun n ↦ ((coeff n F : ℤ) : ℂ) * z ^ n) (intSeriesEval F z)) ∧
    (∀ F (r' : ℝ), IntSeriesConv F r → 0 ≤ r' → r' ≤ r → IntSeriesConv F r') ∧
    (∀ (p : ℕ) (hp : p ≠ 0) F, IntSeriesConv F (r ^ p) →
      IntSeriesConv (expand p hp F) r ∧
        ∀ z : ℂ, ‖z‖ ≤ r → intSeriesEval (expand p hp F) z = intSeriesEval F (z ^ p))
end
end GroundTheory.Heights₂.Heights.ChowlaSelberg


