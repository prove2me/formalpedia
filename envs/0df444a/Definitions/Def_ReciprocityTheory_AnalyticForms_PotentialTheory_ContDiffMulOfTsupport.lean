-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffMulOfTsupport
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffMulOfTsupport
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:57:35.660633+00:00
-- url     : https://prove2.me/theorems/5f80df56-85d5-4c54-b3e2-5290fefd55b1
-- title:
--   Cont Diff Mul Of Tsupport
-- statement:
--   Definitions and structural lemmas for Cont Diff Mul Of Tsupport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffMulOfTsupport.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffHypInclAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt)
open scoped ContDiff Manifold
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
section Helpers
omit [T2Space X] [CompactSpace X]
end Helpers
end
end ReciprocityTheory.AnForm.M.PLAux


