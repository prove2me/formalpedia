-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
-- name    : ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:24.664023+00:00
-- url     : https://prove2.me/theorems/b0bb25e5-a834-475c-99cd-82655581d8f8
-- title:
--   Ext Cut A
-- statement:
--   Definitions and structural lemmas for Ext Cut A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean

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
noncomputable section
def cutL (ε s : ℝ) : ℝ := Real.log (s + ε) - Real.log ε
def cutP (ε s : ℝ) : ℝ := cutL ε s ^ 2 / 2
def halfLogRatioSqDeriv (ε s : ℝ) : ℝ := cutL ε s / (s + ε)
def halfLogRatioSqSecondDeriv (ε s : ℝ) : ℝ := (1 - cutL ε s) / (s + ε) ^ 2
variable {n : ℕ}
def complexLineSecondDeriv (F : V n → ℂ) (z e : V n) : ℂ := deriv (deriv (fun l : ℂ => F (z + l • e))) 0
end
end ReciprocityTheory.L2DbarEstimates.C


