-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData30RightCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData30RightCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:10:12.662648+00:00
-- url     : https://prove2.me/theorems/c7dc6214-7148-4665-aa48-560d0b6a2785
-- title:
--   Small Pair Light Data30Right Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared30.rightCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData30RightCachedChunk02.lean, lines 7-129, SHA-256 4ff1db553c4bc0b2730dae2b550827c481b702d9a7690fca7b86b8ed9f0da482. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_7768cb236ba65f9605a5
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_f8e425b6c4d35d6020b3
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_04fdec1fd0058b6ef032
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_8062b7f4ae5d8c102c38
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_2622cca6d86a4a5647cd
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_7768cb236ba65f9605a5 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_f8e425b6c4d35d6020b3 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_04fdec1fd0058b6ef032 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_8062b7f4ae5d8c102c38 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_2622cca6d86a4a5647cd))))

end D1Bound5.PairLightPrepared30
end


