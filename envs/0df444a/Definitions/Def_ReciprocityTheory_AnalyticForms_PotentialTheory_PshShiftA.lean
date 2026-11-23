-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:39.966593+00:00
-- url     : https://prove2.me/theorems/30f847b4-90ff-4ea6-a236-b0ab3978a497
-- title:
--   Psh Shift A
-- statement:
--   Definitions and structural lemmas for Psh Shift A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
end
end ReciprocityTheory.AnForm


