-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:41.374797+00:00
-- url     : https://prove2.me/theorems/aa466354-8ba8-4918-b166-22180af1dc71
-- title:
--   Fubini Levi
-- statement:
--   Definitions and structural lemmas for Fubini Levi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
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
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {J : Type} [Fintype J]
def sqSum (z : J → ℂ) : ℝ := ∑ p, ‖z p‖ ^ 2
def reInner (a : J → ℂ) : (J → ℂ) →L[ℝ] ℝ :=
  ∑ p, ((a p).re • (Complex.reCLM.comp (ContinuousLinearMap.proj p)) +
    (a p).im • (Complex.imCLM.comp (ContinuousLinearMap.proj p)))
def phi (z : J → ℂ) : ℝ := Real.log (sqSum z) * (1 / 2)
section Line
end Line
end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi


