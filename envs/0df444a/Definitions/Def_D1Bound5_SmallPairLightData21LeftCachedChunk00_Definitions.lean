-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData21LeftCachedChunk00_Definitions
-- name    : D1Bound5_SmallPairLightData21LeftCachedChunk00_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:42:54.930002+00:00
-- url     : https://prove2.me/theorems/96fa8e55-0799-4700-b682-384df9fc2dc6
-- title:
--   Small Pair Light Data21Left Cached Chunk00
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared21.leftCachedChunk00`.
-- source:
--   D1Bound5/SmallPairLightData21LeftCachedChunk00.lean, lines 7-129, SHA-256 443fcf82c6f5610ecbe42cebdc0989fd2d09efdaf00a9718952dfdd017de4280. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_64a32029d6b15d8a20f4
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_d23fd9f93cb79b08bb63
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_00814803254cbc5081dc
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_37d4026e2c862407c7f7
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_2d276e0387795d90a330
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCachedChunk00 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_64a32029d6b15d8a20f4 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_d23fd9f93cb79b08bb63 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_00814803254cbc5081dc (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_37d4026e2c862407c7f7 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_2d276e0387795d90a330))))

end D1Bound5.PairLightPrepared21
end


