-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:42.951518+00:00
-- url     : https://prove2.me/theorems/7d6a38a0-8b5d-4853-8c1e-d985545c4b97
-- title:
--   Projective Line Partition Continuous Coe
-- statement:
--   Definitions and structural lemmas for Projective Line Partition Continuous Coe, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ProjectiveLinePartitionContinuousCoe.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology Set
noncomputable section
def p1i0 : Fin p1.n := ⟨0, by show 0 < 2; norm_num⟩
def p1i1 : Fin p1.n := ⟨1, by show 1 < 2; norm_num⟩
end
end ReciprocityTheory.AnForm.M


