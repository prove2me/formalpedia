-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData8LeftCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:57:02.55269+00:00
-- url     : https://prove2.me/theorems/44539910-f22c-4a9c-a3fa-4871f6305295
-- title:
--   Small Pair Light Data8Left Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared8.leftCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData8LeftCachedChunk02.lean, lines 8-109, SHA-256 339da09141451443433141f9b48ebd3ea0a4609ac1507cc66b395c3257f69a64. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_dd7dfcf19de60bcb6eb9
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_21431c5cc4ed59b5083f
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_cfd026ddbbb9d49242ef
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_f9b137423ae597ebe6a3
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_be9e68bdb1a02891a50c
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_dd7dfcf19de60bcb6eb9 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_21431c5cc4ed59b5083f (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_cfd026ddbbb9d49242ef (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_f9b137423ae597ebe6a3 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_be9e68bdb1a02891a50c))))

end D1Bound5.PairLightPrepared8
end


