-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_HarishChandraMultiplicity_HCMult
-- name    : CompanionTheory_AutomorphicTheory_HarishChandraMultiplicity_HCMult
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:25.657784+00:00
-- url     : https://prove2.me/theorems/695ac368-02c4-407c-aa73-271e8ba859f7
-- title:
--   HCMult
-- statement:
--   Definitions and structural lemmas for HCMult, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HarishChandraMultiplicity/HCMult.lean

import Definitions.Def_Formalism_PeriodIntegrals_HCMult
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinalAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace CompanionTheory.HCMult
open PI.UpqRep CompanionTheory.D.gk.admitted
end CompanionTheory.HCMult


