-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
-- name    : ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:27.855229+00:00
-- url     : https://prove2.me/theorems/fd62ad4e-c3a0-47bd-ac40-a1ec31508dcd
-- title:
--   Integral Bump Prof One Pos
-- statement:
--   Definitions and structural lemmas for Integral Bump Prof One Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/IntegralBumpProfOnePos.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
variable {n : ℕ}
noncomputable def bumpProf (t s : ℝ) : ℝ := Real.smoothTransition (1 - 4 * (s / t) ^ 2)
noncomputable def mollConst (n : ℕ) : ℝ := (∫ z : V n, bumpProf 1 ‖z‖)⁻¹
noncomputable def mollProf (n : ℕ) (t s : ℝ) : ℝ := mollConst n * (t ^ (2 * n))⁻¹ * bumpProf t s
noncomputable def moll (n : ℕ) (t : ℝ) (z : V n) : ℝ := mollProf n t ‖z‖
noncomputable def mollify (n : ℕ) (t : ℝ) (u : V n → ℂ) (x : V n) : ℂ :=
  ∫ y, (moll n t (x - y) : ℂ) * u y
end ReciprocityTheory.L2DbarEstimates.C


