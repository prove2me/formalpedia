-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
-- name    : ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:25.585562+00:00
-- url     : https://prove2.me/theorems/64243e1f-8531-43b0-bad5-7dea3d968fa1
-- title:
--   Ext Weak A
-- statement:
--   Definitions and structural lemmas for Ext Weak A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeakA.lean

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
open scoped ENNReal ContDiff
noncomputable def extCh (t : ℝ) : ℝ := Real.smoothTransition (2 - t)
variable {n : ℕ}
noncomputable def extCut (F : V n → ℂ) (k : ℝ) (z : V n) : ℝ :=
  if F z = 0 then 0 else extCh (-Real.log (‖F z‖ ^ 2) / k)
end ReciprocityTheory.L2DbarEstimates.C


