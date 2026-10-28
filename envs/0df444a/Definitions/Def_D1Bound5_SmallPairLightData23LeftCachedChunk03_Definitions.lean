-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData23LeftCachedChunk03_Definitions
-- name    : D1Bound5_SmallPairLightData23LeftCachedChunk03_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:33:01.180508+00:00
-- url     : https://prove2.me/theorems/01485712-c741-41ce-8088-4fed206288fd
-- title:
--   Small Pair Light Data23Left Cached Chunk03
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared23.leftCachedChunk03`.
-- source:
--   D1Bound5/SmallPairLightData23LeftCachedChunk03.lean, lines 7-129, SHA-256 830b2e597767ea86d4c6c6bde959f2d9d8c93172c3e436198b0b5263f2850ff9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_2e54db19ffb1b7b2c498
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_ad57dc4cdf9686a4761e
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_9acc54bf17c9f0365dea
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_c8b0e7d83b3dbf9a21c3
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_e84cf42ec4d01247b1f5
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCachedChunk03 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_2e54db19ffb1b7b2c498 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_ad57dc4cdf9686a4761e (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_9acc54bf17c9f0365dea (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_c8b0e7d83b3dbf9a21c3 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_e84cf42ec4d01247b1f5))))

end D1Bound5.PairLightPrepared23
end


