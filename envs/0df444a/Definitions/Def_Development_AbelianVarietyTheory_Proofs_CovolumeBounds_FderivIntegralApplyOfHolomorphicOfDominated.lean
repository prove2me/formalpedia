-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:26.616488+00:00
-- url     : https://prove2.me/theorems/e3128b95-6f10-4cc5-a094-c5c7834fc047
-- title:
--   Fderiv Integral Apply Of Holomorphic Of Dominated
-- statement:
--   Definitions and structural lemmas for Fderiv Integral Apply Of Holomorphic Of Dominated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FderivIntegralApplyOfHolomorphicOfDominated.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped Topology Interval
namespace GlobalTheory
variable {T : Type*} [MeasurableSpace T] {μ : Measure T}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [FiniteDimensional ℂ E]
set_option linter.unusedSectionVars false
variable [CompleteSpace V]
end GlobalTheory


