-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeInt
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:18.978296+00:00
-- url     : https://prove2.me/theorems/fe4b71dc-e227-4eac-bb31-2a23937b6fdd
-- title:
--   Degree Int
-- statement:
--   Definitions and structural lemmas for Degree Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeInt.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
end
end ReciprocityTheory.AnForm.M


