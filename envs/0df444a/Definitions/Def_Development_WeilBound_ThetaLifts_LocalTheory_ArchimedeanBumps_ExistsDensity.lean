-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:27.062609+00:00
-- url     : https://prove2.me/theorems/5379cba8-3b16-449e-8abf-136217f88d3b
-- title:
--   Exists Density
-- statement:
--   Definitions and structural lemmas for Exists Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ExistsDensity.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace
variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
def ch (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)
variable [MeasurableSpace X] [BorelSpace X]
end PositivityTheory.ThKG.Loc.Bump
end


