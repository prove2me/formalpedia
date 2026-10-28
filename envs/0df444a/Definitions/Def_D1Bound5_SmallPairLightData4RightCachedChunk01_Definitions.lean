-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData4RightCachedChunk01_Definitions
-- name    : D1Bound5_SmallPairLightData4RightCachedChunk01_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:32:37.732979+00:00
-- url     : https://prove2.me/theorems/5f9cf7b9-a93b-4625-b3ab-9fa199ece106
-- title:
--   Small Pair Light Data4Right Cached Chunk01
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared4.rightCachedChunk01`.
-- source:
--   D1Bound5/SmallPairLightData4RightCachedChunk01.lean, lines 9-110, SHA-256 1e766acabadd343a87bd49e818ae43c04e21d05d23397f8a22bf2c5ccb8f8567. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_93db630df5ce7f6030bb
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_4fb0d7e03d0da5d42eed
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_0e3ac362c3034b2a7c16
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_f34530dbc14eaa8701eb
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_09898728e9dad79fed0e
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


noncomputable def rightCachedChunk01 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_93db630df5ce7f6030bb (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_4fb0d7e03d0da5d42eed (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_0e3ac362c3034b2a7c16 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_f34530dbc14eaa8701eb _root_.D1Bound5.Prove2MeTransfer.cachedSlice_09898728e9dad79fed0e))))

end D1Bound5.PairLightPrepared4
end


