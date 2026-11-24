-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:29.113875+00:00
-- url     : https://prove2.me/theorems/970414bb-c8e5-4530-bd92-e4a079dbd17f
-- title:
--   Psh Reg Max
-- statement:
--   Definitions and structural lemmas for Psh Reg Max, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
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
section RegMaxDeriv
variable {ι : Type*} [Fintype ι] [Nonempty ι]
end RegMaxDeriv
section Psh
variable {ι : Type*} [Fintype ι] [Nonempty ι]
end Psh
section Levi
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
end Levi
end
end ReciprocityTheory.AnForm.A


