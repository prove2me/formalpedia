-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData10LeftCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData10LeftCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:10:12.723572+00:00
-- url     : https://prove2.me/theorems/307e91d8-5598-412f-8b59-554b372fa096
-- title:
--   Small Pair Light Data10Left Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared10.leftCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData10LeftCachedChunk02.lean, lines 8-109, SHA-256 54802555ab1e0e109099d803d44d8faaab25ce4717be9650601e5a43283d373b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_da5676a45e5c69d1ccee
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_f51c9b650efb02c0db1d
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_32fca06fd4f9c06534c3
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_d0d0c0a53704446b3e1c
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_6082c6090142ea1d0a2e
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_da5676a45e5c69d1ccee (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_f51c9b650efb02c0db1d (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_32fca06fd4f9c06534c3 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_d0d0c0a53704446b3e1c _root_.D1Bound5.Prove2MeTransfer.cachedSlice_6082c6090142ea1d0a2e))))

end D1Bound5.PairLightPrepared10
end


