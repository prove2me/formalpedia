-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData28RightCachedChunk04_Definitions
-- name    : D1Bound5_SmallPairLightData28RightCachedChunk04_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:27:17.704588+00:00
-- url     : https://prove2.me/theorems/9a8b862c-0ad1-4ed8-ab77-a4086b0def9f
-- title:
--   Small Pair Light Data28Right Cached Chunk04
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared28.rightCachedChunk04`.
-- source:
--   D1Bound5/SmallPairLightData28RightCachedChunk04.lean, lines 7-53, SHA-256 fc90abf473ec8a24277e1f8fe0ed4fe3c8124200926324b24748f93f6d77494a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_3a69bb7f5c532745fbe0
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_fad9d8752ac85018d5fb
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCachedChunk04 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_3a69bb7f5c532745fbe0 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_fad9d8752ac85018d5fb)

end D1Bound5.PairLightPrepared28
end


