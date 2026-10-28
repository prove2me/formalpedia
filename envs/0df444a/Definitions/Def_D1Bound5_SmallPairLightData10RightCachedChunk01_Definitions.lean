-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData10RightCachedChunk01_Definitions
-- name    : D1Bound5_SmallPairLightData10RightCachedChunk01_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:49:14.596998+00:00
-- url     : https://prove2.me/theorems/04f0f837-2d91-438f-bc6a-9b4f80bd24ca
-- title:
--   Small Pair Light Data10Right Cached Chunk01
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared10.rightCachedChunk01`.
-- source:
--   D1Bound5/SmallPairLightData10RightCachedChunk01.lean, lines 8-109, SHA-256 f5075e6b87cdc257d3829b3277ff9fd4cebad26f509fbc337c6f946d79f2804f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_53b391c6a51b59226256
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_d17247c2e53cea19adc5
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_3b5190c19b0140577ee2
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_8306336666fb6288a019
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_baf7601c7d27c5c7551f
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightCachedChunk01 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_53b391c6a51b59226256 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_d17247c2e53cea19adc5 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_3b5190c19b0140577ee2 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_8306336666fb6288a019 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_baf7601c7d27c5c7551f))))

end D1Bound5.PairLightPrepared10
end


