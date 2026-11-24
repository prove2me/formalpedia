-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:28.410057+00:00
-- url     : https://prove2.me/theorems/2af975d5-55ed-4c46-b2a5-40cd050032da
-- title:
--   Continuous Tmax Shift
-- statement:
--   Definitions and structural lemmas for Continuous Tmax Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
section TMax
variable {ι : Type*} [Fintype ι] [Nonempty ι]
end TMax
section Kernel
variable {ι : Type*} [Fintype ι]
def kK (h : ι → ℝ) : ℝ := ∏ j, kθ (h j)
end Kernel
section RegMaxBasic
variable {ι : Type*} [Fintype ι] [Nonempty ι]
end RegMaxBasic
end
end ReciprocityTheory.AnForm.A


