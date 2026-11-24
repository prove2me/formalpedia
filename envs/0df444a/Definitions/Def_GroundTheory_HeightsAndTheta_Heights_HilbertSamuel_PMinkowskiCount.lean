-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMinkowskiCount
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMinkowskiCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:38.506805+00:00
-- url     : https://prove2.me/theorems/46d9ee55-51ab-42df-b03b-a324fed7d7a9
-- title:
--   PMinkowski Count
-- statement:
--   Definitions and structural lemmas for PMinkowski Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Module Metric
open scoped ENNReal
noncomputable section
namespace MinkowskiCount
section Count
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
end Count
end MinkowskiCount
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


