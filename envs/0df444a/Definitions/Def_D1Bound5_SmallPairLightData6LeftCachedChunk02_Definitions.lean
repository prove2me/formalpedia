-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData6LeftCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData6LeftCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:25:04.619985+00:00
-- url     : https://prove2.me/theorems/69edbb45-25fb-4684-9cdd-c6cc9f340fbc
-- title:
--   Small Pair Light Data6Left Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared6.leftCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData6LeftCachedChunk02.lean, lines 8-109, SHA-256 8ad6aa935be9b353e3f53f3193e0122353bffd58a56acbef3148f4d22f8a3701. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_213b8c22a88d7ec35d5f
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_bef7eb32ec8113db4ecd
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_df3a52a248910cae80ef
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_b1a53ab22e0b7478ee77
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_f228c3610d4f2df858a3
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_213b8c22a88d7ec35d5f (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_bef7eb32ec8113db4ecd (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_df3a52a248910cae80ef (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_b1a53ab22e0b7478ee77 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_f228c3610d4f2df858a3))))

end D1Bound5.PairLightPrepared6
end


