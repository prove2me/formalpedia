-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData21LeftCachedChunk04_Definitions
-- name    : D1Bound5_SmallPairLightData21LeftCachedChunk04_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:44:58.652438+00:00
-- url     : https://prove2.me/theorems/7793b9a8-fb3f-4009-8e5f-89ba8ccb6131
-- title:
--   Small Pair Light Data21Left Cached Chunk04
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared21.leftCachedChunk04`.
-- source:
--   D1Bound5/SmallPairLightData21LeftCachedChunk04.lean, lines 7-53, SHA-256 b00bb8bd5f27bdeac7d2b03ed97286da42a17502ca058acc104fe00b8a74eddb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_077020c72f0389bef7b1
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_a7bd9261609e3be47745
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCachedChunk04 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_077020c72f0389bef7b1 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_a7bd9261609e3be47745)

end D1Bound5.PairLightPrepared21
end


