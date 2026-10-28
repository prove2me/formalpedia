-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData30LeftCachedChunk01_Definitions
-- name    : D1Bound5_SmallPairLightData30LeftCachedChunk01_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:29:53.652657+00:00
-- url     : https://prove2.me/theorems/6ac9c7f3-af1a-4eb7-98fd-76ab594b1cef
-- title:
--   Small Pair Light Data30Left Cached Chunk01
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared30.leftCachedChunk01`.
-- source:
--   D1Bound5/SmallPairLightData30LeftCachedChunk01.lean, lines 7-129, SHA-256 687b4a566b61f40367645adf00c4d545b0db9098a7d77e916e859ba1e259d355. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_f8ff4cc61b415060a216
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_774fd6202ba7739afdd1
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_40d5e83c7b2a910e69e1
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_fca39bfb8153f3589acc
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_8ba7e2927ed7f7784420
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCachedChunk01 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_f8ff4cc61b415060a216 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_774fd6202ba7739afdd1 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_40d5e83c7b2a910e69e1 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_fca39bfb8153f3589acc _root_.D1Bound5.Prove2MeTransfer.cachedSlice_8ba7e2927ed7f7784420))))

end D1Bound5.PairLightPrepared30
end


