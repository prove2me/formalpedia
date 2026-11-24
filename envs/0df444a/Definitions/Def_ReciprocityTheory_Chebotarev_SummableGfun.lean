-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_SummableGfun
-- name    : ReciprocityTheory_Chebotarev_SummableGfun
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:05.558808+00:00
-- url     : https://prove2.me/theorems/fb8eb4ea-5a50-4f21-b1a0-bcf136ac4b40
-- title:
--   Summable Gfun
-- statement:
--   Definitions and structural lemmas for Summable Gfun, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SummableGfun.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA
import Definitions.Def_ReciprocityTheory_Chebotarev_CTrick
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.Units Filter Topology Set
open scoped Classical
namespace ReciprocityTheory.Cheb
end ReciprocityTheory.Cheb


