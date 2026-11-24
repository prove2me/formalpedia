-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
-- name    : ReciprocityTheory_Chebotarev_UnitPart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:17.195553+00:00
-- url     : https://prove2.me/theorems/12d81b05-cb4f-46d6-a881-aa603be182c1
-- title:
--   Unit Part
-- statement:
--   Definitions and structural lemmas for Unit Part, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/UnitPart.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
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


