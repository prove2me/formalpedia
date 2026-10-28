-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk03_Definitions
-- name    : D1Bound5_SmallPairLightData8LeftCachedChunk03_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:02:26.350822+00:00
-- url     : https://prove2.me/theorems/37f9fdef-76a9-4342-8a9a-0260560d28ea
-- title:
--   Small Pair Light Data8Left Cached Chunk03
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared8.leftCachedChunk03`.
-- source:
--   D1Bound5/SmallPairLightData8LeftCachedChunk03.lean, lines 8-109, SHA-256 4a402a0e38eafe94f48bd7f2af8c561f6403fb962c86655df895fdb2062fbae0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_fdfaef2e1f455e52b6f7
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_491ab98fe3a2f33e2183
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_6b08a95adc0f6140cd54
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_77dd1f49dda98d713795
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_706266ec1edf54450ebd
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCachedChunk03 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_fdfaef2e1f455e52b6f7 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_491ab98fe3a2f33e2183 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_6b08a95adc0f6140cd54 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_77dd1f49dda98d713795 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_706266ec1edf54450ebd))))

end D1Bound5.PairLightPrepared8
end


