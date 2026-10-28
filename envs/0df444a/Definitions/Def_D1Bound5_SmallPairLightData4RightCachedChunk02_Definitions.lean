-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData4RightCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData4RightCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:02:22.529099+00:00
-- url     : https://prove2.me/theorems/81d0fc6c-b51d-46e7-9912-9d1a22608463
-- title:
--   Small Pair Light Data4Right Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared4.rightCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData4RightCachedChunk02.lean, lines 9-110, SHA-256 6e8b4c0eb7c8210875fdda7bb6b5cae6a6db727a57f0bea006bad4a22d0835f6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_ab29adc0346b551340e7
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_2c7b157374cf7c5e7f02
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_244224fae589a1b80c7d
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_d0ae488c850046c36f3f
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_82111bfe145d25a11191
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


noncomputable def rightCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_ab29adc0346b551340e7 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_2c7b157374cf7c5e7f02 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_244224fae589a1b80c7d (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_d0ae488c850046c36f3f _root_.D1Bound5.Prove2MeTransfer.cachedSlice_82111bfe145d25a11191))))

end D1Bound5.PairLightPrepared4
end


