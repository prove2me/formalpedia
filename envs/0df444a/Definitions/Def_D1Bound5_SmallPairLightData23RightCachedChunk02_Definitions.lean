-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData23RightCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData23RightCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:42:49.905785+00:00
-- url     : https://prove2.me/theorems/31dae53e-c443-4e1a-9ce6-f66ad29c011f
-- title:
--   Small Pair Light Data23Right Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared23.rightCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData23RightCachedChunk02.lean, lines 7-129, SHA-256 b107e9420b2f282625048cbb0eb1d7da368f6e886fd4236ce7dcfca503ba08f3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_409de6551f327e2cd758
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_116a112be3680bdde083
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_7c4e52fdf09f6a2baefb
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_3d65babebb44e8c00395
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_ec86ff64599f7642d900
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_409de6551f327e2cd758 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_116a112be3680bdde083 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_7c4e52fdf09f6a2baefb (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_3d65babebb44e8c00395 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_ec86ff64599f7642d900))))

end D1Bound5.PairLightPrepared23
end


