-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData14LeftCachedChunk01_Definitions
-- name    : D1Bound5_SmallPairLightData14LeftCachedChunk01_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:31:39.437079+00:00
-- url     : https://prove2.me/theorems/c05104bf-4798-4aa2-8fab-6a3dab5670f6
-- title:
--   Small Pair Light Data14Left Cached Chunk01
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared14.leftCachedChunk01`.
-- source:
--   D1Bound5/SmallPairLightData14LeftCachedChunk01.lean, lines 7-129, SHA-256 0a7102f5aad780905ebea69337ce74b851ab0635d1ae3094eaf81c572ffc5ce4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_4948a46f49b20588a095
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_e819b7c7eb226d1e8877
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_2fde66ea137de2dbaff7
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_4ceed1a30e7c16152e62
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_1a8b53945c7e912e57b4
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCachedChunk01 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_4948a46f49b20588a095 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_e819b7c7eb226d1e8877 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_2fde66ea137de2dbaff7 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_4ceed1a30e7c16152e62 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_1a8b53945c7e912e57b4))))

end D1Bound5.PairLightPrepared14
end


