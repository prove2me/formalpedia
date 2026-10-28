-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData6RightCachedChunk01_Definitions
-- name    : D1Bound5_SmallPairLightData6RightCachedChunk01_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:26:08.590053+00:00
-- url     : https://prove2.me/theorems/e0fa9bce-cd91-4033-b72e-5acd2bd3b740
-- title:
--   Small Pair Light Data6Right Cached Chunk01
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared6.rightCachedChunk01`.
-- source:
--   D1Bound5/SmallPairLightData6RightCachedChunk01.lean, lines 8-109, SHA-256 b396387b589671ce92f60470b28ab6d48727673f75231fce909200c564b734c3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_b864c154022b2683c265
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_814a7fa0e5fef6977d24
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_b0f075c351434b48ea07
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_debb3bcfac6cc03f9122
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_b6fbe590ca1f1ee2df71
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightCachedChunk01 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_b864c154022b2683c265 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_814a7fa0e5fef6977d24 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_b0f075c351434b48ea07 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_debb3bcfac6cc03f9122 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_b6fbe590ca1f1ee2df71))))

end D1Bound5.PairLightPrepared6
end


