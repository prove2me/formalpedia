-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
-- name    : GroundTheory_AutomorphicForms_ReductionIdele
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:54:22.690585+00:00
-- url     : https://prove2.me/theorems/9a84d485-0c45-5345-9772-05209950a0be
-- title:
--   Reduction Idele
-- statement:
--   Definitions and structural lemmas for Reduction Idele, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIdele.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Set
open GroundTheory.Global GroundTheory.Global.IdeleGroup
namespace GroundTheory.Automorphic
namespace Reduction
variable {K : Type*} [Field K] [NumberField K]
end Reduction
end GroundTheory.Automorphic


