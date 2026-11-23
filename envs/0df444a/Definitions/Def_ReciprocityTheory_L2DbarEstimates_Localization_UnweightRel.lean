-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
-- name    : ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:33.397317+00:00
-- url     : https://prove2.me/theorems/aaa219bb-4790-4b01-9b97-09f97af88650
-- title:
--   Unweight Rel
-- statement:
--   Definitions and structural lemmas for Unweight Rel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
section UnweightRelAux
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
end UnweightRelAux
end
end ReciprocityTheory.L2DbarEstimates.F


