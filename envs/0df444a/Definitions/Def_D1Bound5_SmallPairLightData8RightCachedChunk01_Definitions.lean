-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData8RightCachedChunk01_Definitions
-- name    : D1Bound5_SmallPairLightData8RightCachedChunk01_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:51:55.558563+00:00
-- url     : https://prove2.me/theorems/6b14e7e4-0b24-4f2b-99d7-7a6177c7da55
-- title:
--   Small Pair Light Data8Right Cached Chunk01
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared8.rightCachedChunk01`.
-- source:
--   D1Bound5/SmallPairLightData8RightCachedChunk01.lean, lines 8-109, SHA-256 a667679bb90870cb4a14093cb97a997948395a416c4f3a654f273608e5bdab53. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_b76b750e31b9314c5269
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_4364071b287a0f43de17
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_522d5b93c35869211fb3
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_09b5942f3c762d1e617c
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_dcaae06a09437f12259c
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightCachedChunk01 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_b76b750e31b9314c5269 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_4364071b287a0f43de17 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_522d5b93c35869211fb3 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_09b5942f3c762d1e617c _root_.D1Bound5.Prove2MeTransfer.cachedSlice_dcaae06a09437f12259c))))

end D1Bound5.PairLightPrepared8
end


