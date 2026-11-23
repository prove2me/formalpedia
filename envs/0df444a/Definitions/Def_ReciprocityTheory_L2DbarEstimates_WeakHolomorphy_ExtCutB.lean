-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
-- name    : ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:06.38137+00:00
-- url     : https://prove2.me/theorems/a9f89086-f948-41ad-aa62-10325d7c39ed
-- title:
--   Ext Cut B
-- statement:
--   Definitions and structural lemmas for Ext Cut B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
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
noncomputable section
variable {n : ℕ}
def lineFirstVariation (ε : ℝ) (x y : ℂ) : ℝ := halfLogRatioSqDeriv ε (‖x‖ ^ 2) * (2 * inner ℝ x y)
def lineSecondVariation (ε : ℝ) (x y w : ℂ) : ℝ :=
  halfLogRatioSqSecondDeriv ε (‖x‖ ^ 2) * (2 * inner ℝ x y) * (2 * inner ℝ x y) +
    halfLogRatioSqDeriv ε (‖x‖ ^ 2) * (2 * (inner ℝ x w + inner ℝ y y))
end
end ReciprocityTheory.L2DbarEstimates.C


