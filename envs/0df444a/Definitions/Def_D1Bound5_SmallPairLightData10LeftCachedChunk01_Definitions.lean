-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData10LeftCachedChunk01_Definitions
-- name    : D1Bound5_SmallPairLightData10LeftCachedChunk01_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:06:22.206995+00:00
-- url     : https://prove2.me/theorems/2d7fd06d-3e1f-4293-9bcd-93c3272eaaac
-- title:
--   Small Pair Light Data10Left Cached Chunk01
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared10.leftCachedChunk01`.
-- source:
--   D1Bound5/SmallPairLightData10LeftCachedChunk01.lean, lines 8-109, SHA-256 0d79e4840a305324e1708fb7c800dafd7ba884b236bea27519f4e1e9473b2071. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_ea46ecd2a784040a3b61
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_013bdbd50f0df1e9376a
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_3e0ae654039411db7c34
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_43fa5e4b4d675794aa23
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_e1611ec8e9fed68dee32
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCachedChunk01 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_ea46ecd2a784040a3b61 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_013bdbd50f0df1e9376a (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_3e0ae654039411db7c34 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_43fa5e4b4d675794aa23 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_e1611ec8e9fed68dee32))))

end D1Bound5.PairLightPrepared10
end


