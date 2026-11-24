-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartQuot
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartQuot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:11.906195+00:00
-- url     : https://prove2.me/theorems/c2756668-7edb-431a-afe1-facfad672573
-- title:
--   PSpec Chart Quot
-- statement:
--   Definitions and structural lemmas for PSpec Chart Quot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartQuot.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
noncomputable section
namespace SpecChart
variable {A : Type*} [CommRing A] (W : Ideal A) [W.IsPrime] (P : Ideal A)
end SpecChart
end
end GroundTheory.Heights₂.Heights.Vertical


