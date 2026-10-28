-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk00_Definitions
-- name    : D1Bound5_SmallPairLightData8LeftCachedChunk00_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:42:50.93626+00:00
-- url     : https://prove2.me/theorems/310caa0d-6ae3-47d1-8952-72e8bf13777a
-- title:
--   Small Pair Light Data8Left Cached Chunk00
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared8.leftCachedChunk00`.
-- source:
--   D1Bound5/SmallPairLightData8LeftCachedChunk00.lean, lines 8-109, SHA-256 f73ed11c8f9836ce5545e12664005f76fc5297491b33153c5db00db7e0411d8f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_5bebdeb6560770c27103
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_80b0bbe43cb5e9494c4c
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_252c9d9aad4f6132e426
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_becf67414d3208123d94
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_57318734c079640770c6
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCachedChunk00 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_5bebdeb6560770c27103 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_80b0bbe43cb5e9494c4c (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_252c9d9aad4f6132e426 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_becf67414d3208123d94 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_57318734c079640770c6))))

end D1Bound5.PairLightPrepared8
end


