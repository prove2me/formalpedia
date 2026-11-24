-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_Support
-- name    : ReciprocityTheory_Chebotarev_Support
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:17.42967+00:00
-- url     : https://prove2.me/theorems/386153cf-c520-48b5-a355-1125af25d6c6
-- title:
--   Support
-- statement:
--   Definitions and structural lemmas for Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/Support.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
namespace ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
end ReciprocityTheory.Cheb


