-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData14LeftCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData14LeftCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:24:10.568062+00:00
-- url     : https://prove2.me/theorems/f9e46dae-c83a-4de5-8f72-c9b23ad82289
-- title:
--   Small Pair Light Data14Left Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared14.leftCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData14LeftCachedChunk02.lean, lines 7-129, SHA-256 32834e39511dd778e361c3c839d53a01fd00494d2681d37b101e4636386f8657. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_d3966e17506624d4cba8
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_c15220b2271c7507052b
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_1e8f62d9a8641588c806
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_3e9286a173851be875af
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_e96210256a50682da5e3
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_d3966e17506624d4cba8 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_c15220b2271c7507052b (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_1e8f62d9a8641588c806 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_3e9286a173851be875af _root_.D1Bound5.Prove2MeTransfer.cachedSlice_e96210256a50682da5e3))))

end D1Bound5.PairLightPrepared14
end


