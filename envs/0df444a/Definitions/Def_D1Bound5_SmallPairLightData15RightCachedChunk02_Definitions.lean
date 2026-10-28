-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData15RightCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData15RightCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:31:46.122998+00:00
-- url     : https://prove2.me/theorems/1fc32cab-c24d-438c-99a7-0f3fd46eb7c4
-- title:
--   Small Pair Light Data15Right Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared15.rightCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData15RightCachedChunk02.lean, lines 7-129, SHA-256 a65c8af746122d1f44378bc3dcfa644fa5a092bef7e42f5a9429113606ec6234. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_e3f5f5959e7597e097a5
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_fe53790203ad6ad197e9
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_5548cb6c2513f2a2d6b1
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_84ec70c7c462f32494dd
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_ac272a1aabc3a9cf79b8
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_e3f5f5959e7597e097a5 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_fe53790203ad6ad197e9 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_5548cb6c2513f2a2d6b1 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_84ec70c7c462f32494dd _root_.D1Bound5.Prove2MeTransfer.cachedSlice_ac272a1aabc3a9cf79b8))))

end D1Bound5.PairLightPrepared15
end


