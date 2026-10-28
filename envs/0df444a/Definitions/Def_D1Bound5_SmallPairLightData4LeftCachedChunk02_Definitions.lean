-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData4LeftCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData4LeftCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:02:25.052147+00:00
-- url     : https://prove2.me/theorems/561a52da-f790-45fe-b675-b592225d6520
-- title:
--   Small Pair Light Data4Left Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared4.leftCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData4LeftCachedChunk02.lean, lines 9-110, SHA-256 231da52fa957b5ff69d2d92cb74a3da9f3228b9f57cebc9c1600306ca49adfd3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_eb6d7a8e6f8e87e39257
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_629d37f0aa3996f257b5
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_46b39b5bcb82203d524d
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_32fdc59b97dc7b58635c
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_b76de3322e80ee08718b
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


noncomputable def leftCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_eb6d7a8e6f8e87e39257 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_629d37f0aa3996f257b5 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_46b39b5bcb82203d524d (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_32fdc59b97dc7b58635c _root_.D1Bound5.Prove2MeTransfer.cachedSlice_b76de3322e80ee08718b))))

end D1Bound5.PairLightPrepared4
end


