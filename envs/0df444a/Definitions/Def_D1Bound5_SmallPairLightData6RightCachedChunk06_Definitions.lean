-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData6RightCachedChunk06_Definitions
-- name    : D1Bound5_SmallPairLightData6RightCachedChunk06_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:54:26.341095+00:00
-- url     : https://prove2.me/theorems/be79f46e-ed2c-476b-974f-e0595bbb0036
-- title:
--   Small Pair Light Data6Right Cached Chunk06
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared6.rightCachedChunk06`.
-- source:
--   D1Bound5/SmallPairLightData6RightCachedChunk06.lean, lines 8-66, SHA-256 4cd5eefa3f200f3d4e080d19a82479c1e20c4e2699a289e64e7aa9d14890c7c3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_8cd4f962c083e6db2500
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_75ae9abd258def5d40a9
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_048650706a6dc3e296d0
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightCachedChunk06 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_8cd4f962c083e6db2500 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_75ae9abd258def5d40a9 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_048650706a6dc3e296d0))

end D1Bound5.PairLightPrepared6
end


