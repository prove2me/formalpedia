-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData10RightCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData10RightCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:49:08.704866+00:00
-- url     : https://prove2.me/theorems/54525c5f-fd00-4006-9237-ce68fa843bdb
-- title:
--   Small Pair Light Data10Right Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared10.rightCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData10RightCachedChunk02.lean, lines 8-109, SHA-256 a8f6f5e8e2a07d77e146b504b79f8407be6f17ea244bbf16c1d9d864e2f6aefd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_ad74f7d00d58ed13e67d
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_e061b0fcd14506c64217
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_6d74e3c3f7c14ac011bd
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_9325ebff0aa78db96a40
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_0ab1773eee7fc034e039
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_ad74f7d00d58ed13e67d (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_e061b0fcd14506c64217 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_6d74e3c3f7c14ac011bd (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_9325ebff0aa78db96a40 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_0ab1773eee7fc034e039))))

end D1Bound5.PairLightPrepared10
end


