-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalB
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:13.930921+00:00
-- url     : https://prove2.me/theorems/3ff06655-d8db-4433-ae2f-8c9ee36b0b56
-- title:
--   Local B
-- statement:
--   Definitions and structural lemmas for Local B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/LocalB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Set
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
section PathL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end PathL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end ReciprocityTheory.ChartRestriction.DS.S7


