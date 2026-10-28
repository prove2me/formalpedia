-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData6RightCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData6RightCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:07:14.189239+00:00
-- url     : https://prove2.me/theorems/c3d4ac08-b055-491c-8766-95143a577be4
-- title:
--   Small Pair Light Data6Right Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared6.rightCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData6RightCachedChunk02.lean, lines 8-109, SHA-256 f57262cd56962106b6a9614a7116024d3dae4a6b4460b8378fb1958060953a6b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_498b68c397fea7749357
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_8f5c0f3845dab4db9934
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_e72a1017e5fcabd6ff05
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_ed5e29b634d63bf7704b
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_238e5992b6cdfe2309bd
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_498b68c397fea7749357 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_8f5c0f3845dab4db9934 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_e72a1017e5fcabd6ff05 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_ed5e29b634d63bf7704b _root_.D1Bound5.Prove2MeTransfer.cachedSlice_238e5992b6cdfe2309bd))))

end D1Bound5.PairLightPrepared6
end


