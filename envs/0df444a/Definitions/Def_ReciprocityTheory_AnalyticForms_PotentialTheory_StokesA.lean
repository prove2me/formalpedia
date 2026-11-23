-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:33.024518+00:00
-- url     : https://prove2.me/theorems/d7272a23-94b6-408a-9b0d-de38625988c9
-- title:
--   Stokes A
-- statement:
--   Definitions and structural lemmas for Stokes A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesA.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
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
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
end
end ReciprocityTheory.AnForm.M


