-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero
-- name    : ReciprocityTheory_Chebotarev_MeanZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:42.261873+00:00
-- url     : https://prove2.me/theorems/732097fc-1009-4c7a-8847-97ab942ea714
-- title:
--   Mean Zero
-- statement:
--   Definitions and structural lemmas for Mean Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/MeanZero.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_NormCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
namespace ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
end ReciprocityTheory.Cheb


