-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData15LeftCachedChunk01_Definitions
-- name    : D1Bound5_SmallPairLightData15LeftCachedChunk01_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:46:33.268741+00:00
-- url     : https://prove2.me/theorems/942e60a5-bc79-450f-a3a6-5c820c12c9d2
-- title:
--   Small Pair Light Data15Left Cached Chunk01
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared15.leftCachedChunk01`.
-- source:
--   D1Bound5/SmallPairLightData15LeftCachedChunk01.lean, lines 7-129, SHA-256 62ece7e1687dec18eedc49cf922a4eada38b7e3c380618351238923f98197d1e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_1db8c96d7678c62a69df
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_509843a4b9b1aaa013bb
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_15df5583eb1d65498147
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_76fc001bc34b141fba0e
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_94cbdde236267206ddf7
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCachedChunk01 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_1db8c96d7678c62a69df (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_509843a4b9b1aaa013bb (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_15df5583eb1d65498147 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_76fc001bc34b141fba0e _root_.D1Bound5.Prove2MeTransfer.cachedSlice_94cbdde236267206ddf7))))

end D1Bound5.PairLightPrepared15
end


