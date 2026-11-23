-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:26.870029+00:00
-- url     : https://prove2.me/theorems/31ea47e3-debd-4d85-982e-9218617d9180
-- title:
--   Schwartz Vanishing Decomposition
-- statement:
--   Definitions and structural lemmas for Schwartz Vanishing Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzVanishingDecomposition.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory Set Filter Topology Metric
noncomputable section
namespace GlobalTheory.SchwartzDiv
section Param
variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}
end Param
def invCut (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1) * t⁻¹
end GlobalTheory.SchwartzDiv
namespace GlobalTheory.SchwartzDiv
end GlobalTheory.SchwartzDiv


