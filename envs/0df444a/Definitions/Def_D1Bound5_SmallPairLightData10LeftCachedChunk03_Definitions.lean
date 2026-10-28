-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData10LeftCachedChunk03_Definitions
-- name    : D1Bound5_SmallPairLightData10LeftCachedChunk03_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:29:19.331974+00:00
-- url     : https://prove2.me/theorems/e5e7ee7f-6fe0-4b5f-83f1-981bb5280ba4
-- title:
--   Small Pair Light Data10Left Cached Chunk03
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared10.leftCachedChunk03`.
-- source:
--   D1Bound5/SmallPairLightData10LeftCachedChunk03.lean, lines 8-109, SHA-256 bd92dffdbe2919231e87f70515bf8233ad1f90c741dda09e4370216501baa98e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_b50329539c12f62cf7cb
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_e5eb06e6e824257cb77e
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_b8de8e63b65921810ee4
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_17926ad1a70b2b5e9a35
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_4017725e45c3e96199d7
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCachedChunk03 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_b50329539c12f62cf7cb (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_e5eb06e6e824257cb77e (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_b8de8e63b65921810ee4 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_17926ad1a70b2b5e9a35 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_4017725e45c3e96199d7))))

end D1Bound5.PairLightPrepared10
end


