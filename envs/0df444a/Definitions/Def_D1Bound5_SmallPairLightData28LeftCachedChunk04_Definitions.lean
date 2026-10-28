-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData28LeftCachedChunk04_Definitions
-- name    : D1Bound5_SmallPairLightData28LeftCachedChunk04_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:46:25.362214+00:00
-- url     : https://prove2.me/theorems/f5bbe68a-bb20-4825-b52e-f0ced7042e22
-- title:
--   Small Pair Light Data28Left Cached Chunk04
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared28.leftCachedChunk04`.
-- source:
--   D1Bound5/SmallPairLightData28LeftCachedChunk04.lean, lines 7-53, SHA-256 d1bf8aad4a7016f8ee0b18d5ebee471b62392b3bce81bdf080879fb9110ebec8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_6fbbba53f34a6a8a3820
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_2a02035fa970665e9ae4
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCachedChunk04 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_6fbbba53f34a6a8a3820 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_2a02035fa970665e9ae4)

end D1Bound5.PairLightPrepared28
end


