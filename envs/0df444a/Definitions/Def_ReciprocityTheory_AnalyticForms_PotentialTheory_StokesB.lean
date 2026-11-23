-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:28.219881+00:00
-- url     : https://prove2.me/theorems/36718013-5bf5-477b-b973-7a9d7c90233f
-- title:
--   Stokes B
-- statement:
--   Definitions and structural lemmas for Stokes B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesB.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
end
end ReciprocityTheory.AnForm.M


