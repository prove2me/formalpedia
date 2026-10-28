-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData30LeftCachedChunk00_Definitions
-- name    : D1Bound5_SmallPairLightData30LeftCachedChunk00_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:18:31.116142+00:00
-- url     : https://prove2.me/theorems/9cd0f461-a97e-4907-859f-3c7c41eff843
-- title:
--   Small Pair Light Data30Left Cached Chunk00
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared30.leftCachedChunk00`.
-- source:
--   D1Bound5/SmallPairLightData30LeftCachedChunk00.lean, lines 7-129, SHA-256 0d29aaaa38a5e721176f46cdcbdb7540d386f7f81f410060da37ebdf92d0a835. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_5b0d6507d9d698d0c9fc
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_29e751450ad79aaf7c55
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_321123bf1c9fd6d9fb52
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_066dc175975e2d05738c
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_d586399c6fedd02b3c67
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCachedChunk00 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_5b0d6507d9d698d0c9fc (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_29e751450ad79aaf7c55 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_321123bf1c9fd6d9fb52 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_066dc175975e2d05738c _root_.D1Bound5.Prove2MeTransfer.cachedSlice_d586399c6fedd02b3c67))))

end D1Bound5.PairLightPrepared30
end


