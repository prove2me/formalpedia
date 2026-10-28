-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData10RightCachedChunk05_Definitions
-- name    : D1Bound5_SmallPairLightData10RightCachedChunk05_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:31:43.669152+00:00
-- url     : https://prove2.me/theorems/c304f322-2672-4a33-bea7-4b95e610a51c
-- title:
--   Small Pair Light Data10Right Cached Chunk05
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared10.rightCachedChunk05`.
-- source:
--   D1Bound5/SmallPairLightData10RightCachedChunk05.lean, lines 8-105, SHA-256 c30bf8f944138aca21fd4db7c95b057c0aea0395e6a6d8d1df5b7feb3fb381e2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_e952686dae547bf98a43
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_e6833c52c136f00b2ee9
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_e851c03a0a5ffca1aba5
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_b0371ff7f8d70aac4960
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightCachedChunk05 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_e952686dae547bf98a43 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_e6833c52c136f00b2ee9 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_e851c03a0a5ffca1aba5 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_b0371ff7f8d70aac4960)))

end D1Bound5.PairLightPrepared10
end


