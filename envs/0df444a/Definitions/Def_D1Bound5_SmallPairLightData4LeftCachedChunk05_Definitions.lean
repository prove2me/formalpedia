-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData4LeftCachedChunk05_Definitions
-- name    : D1Bound5_SmallPairLightData4LeftCachedChunk05_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:44:52.60699+00:00
-- url     : https://prove2.me/theorems/6598fa7c-9767-46f6-89ca-323fc7581c79
-- title:
--   Small Pair Light Data4Left Cached Chunk05
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared4.leftCachedChunk05`.
-- source:
--   D1Bound5/SmallPairLightData4LeftCachedChunk05.lean, lines 9-106, SHA-256 2c6c14f2e8c6d46f13fa3cdf0d6aeb351fb5f1768382dcf13334537a0a16df20. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_04e49509313876b28cb6
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_ac344dd3c1f21282616d
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_5e924681d42a6bd1c8a9
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_a7a01690a0f992e639a0
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


noncomputable def leftCachedChunk05 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_04e49509313876b28cb6 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_ac344dd3c1f21282616d (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_5e924681d42a6bd1c8a9 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_a7a01690a0f992e639a0)))

end D1Bound5.PairLightPrepared4
end


