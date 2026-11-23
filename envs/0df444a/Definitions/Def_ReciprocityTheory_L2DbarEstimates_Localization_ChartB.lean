-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartB
-- name    : ReciprocityTheory_L2DbarEstimates_Localization_ChartB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:18.037037+00:00
-- url     : https://prove2.me/theorems/9f136771-ff8d-475e-bf1e-913f11c76a32
-- title:
--   Chart B
-- statement:
--   Definitions and structural lemmas for Chart B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartB.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
section Main
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}
end Main
section Main
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}
end Main
end
end ReciprocityTheory.L2DbarEstimates.F


