-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData21LeftCachedChunk01_Definitions
-- name    : D1Bound5_SmallPairLightData21LeftCachedChunk01_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:41:09.21293+00:00
-- url     : https://prove2.me/theorems/c2039ad3-fdf3-41de-a3a2-411c1e29342f
-- title:
--   Small Pair Light Data21Left Cached Chunk01
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared21.leftCachedChunk01`.
-- source:
--   D1Bound5/SmallPairLightData21LeftCachedChunk01.lean, lines 7-129, SHA-256 9e644dc00757d29fe5d674e9ea3b59cd2bba8636097ce4e0ffac4c0fad846307. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_1f0891f8b86bf297074d
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_bec15163ba2c4d41b088
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_d40734059ee20dc6d1a6
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_1d838740634402475c97
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_369d06f62a1bec0d0023
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCachedChunk01 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_1f0891f8b86bf297074d (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_bec15163ba2c4d41b088 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_d40734059ee20dc6d1a6 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_1d838740634402475c97 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_369d06f62a1bec0d0023))))

end D1Bound5.PairLightPrepared21
end


