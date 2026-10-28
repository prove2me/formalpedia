-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk04_Definitions
-- name    : D1Bound5_SmallPairLightData8LeftCachedChunk04_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:28:58.808846+00:00
-- url     : https://prove2.me/theorems/5426c0c1-032e-4f84-97df-1ac85da72112
-- title:
--   Small Pair Light Data8Left Cached Chunk04
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared8.leftCachedChunk04`.
-- source:
--   D1Bound5/SmallPairLightData8LeftCachedChunk04.lean, lines 8-109, SHA-256 6cd5e312e7648644074771d9d98f8cbc0b37ae2d52cc32adf93e84a0642ec4c7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_f23efc96aa9ee72bee21
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_8b2b1b37c1bb07594d84
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_90d2b2afbf2695a5a825
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_86475ce7a563e2afb22f
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_219a7a65a7dc2a21b74c
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCachedChunk04 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_f23efc96aa9ee72bee21 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_8b2b1b37c1bb07594d84 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_90d2b2afbf2695a5a825 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_86475ce7a563e2afb22f _root_.D1Bound5.Prove2MeTransfer.cachedSlice_219a7a65a7dc2a21b74c))))

end D1Bound5.PairLightPrepared8
end


