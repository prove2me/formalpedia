-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData6LeftCachedChunk03_Definitions
-- name    : D1Bound5_SmallPairLightData6LeftCachedChunk03_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:11:38.65967+00:00
-- url     : https://prove2.me/theorems/8d724db3-fca8-40e4-8e32-b30784c9d902
-- title:
--   Small Pair Light Data6Left Cached Chunk03
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared6.leftCachedChunk03`.
-- source:
--   D1Bound5/SmallPairLightData6LeftCachedChunk03.lean, lines 8-109, SHA-256 dc7f3893a3850766d6412c9cd648069cbfab541145070a1710dbf6d8d5a5f8d1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_c8cb01383d7f52ce8467
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_746a8e82226c808afbd9
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_22e24f8fe906a4344c6b
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_a6f06f92fd3ca4d75c0c
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_a1ffcecce83096f8ada6
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCachedChunk03 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_c8cb01383d7f52ce8467 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_746a8e82226c808afbd9 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_22e24f8fe906a4344c6b (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_a6f06f92fd3ca4d75c0c _root_.D1Bound5.Prove2MeTransfer.cachedSlice_a1ffcecce83096f8ada6))))

end D1Bound5.PairLightPrepared6
end


