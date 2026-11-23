-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:58.034342+00:00
-- url     : https://prove2.me/theorems/d3c6eb73-8b01-47dd-b0ac-51a91eb54aa4
-- title:
--   Potential Cont Diff At
-- statement:
--   Definitions and structural lemmas for Potential Cont Diff At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PotentialContDiffAt.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
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
open scoped ContDiff ComplexOrder
noncomputable section
section Chart
variable {e : ℕ} {X : Type} [TopologicalSpace X]
end Chart
end
end ReciprocityTheory.AnForm.M


