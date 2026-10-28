-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData30RightCachedChunk01_Definitions
-- name    : D1Bound5_SmallPairLightData30RightCachedChunk01_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:50:35.110186+00:00
-- url     : https://prove2.me/theorems/22968a3c-aabc-41a7-8c28-c782c3bbc54a
-- title:
--   Small Pair Light Data30Right Cached Chunk01
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared30.rightCachedChunk01`.
-- source:
--   D1Bound5/SmallPairLightData30RightCachedChunk01.lean, lines 7-129, SHA-256 e81c9333f2aff1efb8c90a02f1d860c4fb63ce44afd97539d476973e6b579263. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_6ff64b7cb892220d6b03
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_d697b427a827052e33aa
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_b01aaf13a1905d459d6f
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_4f0bb5f80d0968098dca
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_9310de8701c09597e0a7
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCachedChunk01 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_6ff64b7cb892220d6b03 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_d697b427a827052e33aa (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_b01aaf13a1905d459d6f (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_4f0bb5f80d0968098dca _root_.D1Bound5.Prove2MeTransfer.cachedSlice_9310de8701c09597e0a7))))

end D1Bound5.PairLightPrepared30
end


