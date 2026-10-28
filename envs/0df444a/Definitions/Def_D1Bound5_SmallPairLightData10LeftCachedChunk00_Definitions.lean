-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData10LeftCachedChunk00_Definitions
-- name    : D1Bound5_SmallPairLightData10LeftCachedChunk00_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:24:51.485648+00:00
-- url     : https://prove2.me/theorems/a534ae18-c3d7-441f-a920-100ab468512c
-- title:
--   Small Pair Light Data10Left Cached Chunk00
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared10.leftCachedChunk00`.
-- source:
--   D1Bound5/SmallPairLightData10LeftCachedChunk00.lean, lines 8-109, SHA-256 b957167f539023e9c614d9d664f79a787f3691ee0da7bbea7c0528f4ef02156d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_579f94eea3602b5f1ab1
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_774d6128c6d21bcbda9a
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_c41b50a99ea087570822
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_878643aa38d4e077686a
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_da5e8664e9468d250571
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCachedChunk00 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_579f94eea3602b5f1ab1 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_774d6128c6d21bcbda9a (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_c41b50a99ea087570822 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_878643aa38d4e077686a _root_.D1Bound5.Prove2MeTransfer.cachedSlice_da5e8664e9468d250571))))

end D1Bound5.PairLightPrepared10
end


