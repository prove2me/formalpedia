-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:58.327247+00:00
-- url     : https://prove2.me/theorems/bdd908e9-e33f-4dff-8a83-ef268b8a880c
-- title:
--   Reg Max A
-- statement:
--   Definitions and structural lemmas for Reg Max A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
def rmStep (t : ℝ) : ℝ := 2 * Real.smoothTransition (t + 1 / 2) - 1
def rmPrim (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, rmStep s
def rmRho0 (t : ℝ) : ℝ := (rmPrim t + rmPrim (-t)) / 2
def rmRho (t : ℝ) : ℝ := rmRho0 t + (1 / 2 - rmRho0 (1 / 2))
def rmRho' (t : ℝ) : ℝ := (rmStep t - rmStep (-t)) / 2
variable {n : ℕ}
def rmVec (ξ : Fin n → ℂ) : V n := ∑ j, ξ j • bas n j
end
end ReciprocityTheory.L2DbarEstimates.Y


