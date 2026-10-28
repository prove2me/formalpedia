-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_003
-- name    : D1Bound5_SmallPairLightData26_Definitions_003
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:50:29.869113+00:00
-- url     : https://prove2.me/theorems/7e855e5c-392e-4b32-a300-eb4039e1c49f
-- title:
--   Small Pair Light Data26 003
-- statement:
--   Exact finite data for the small-pair square tests and mutation graphs. The named objects in this bundle include `PairLightPrepared26.data26SplitV1_leftCached_09`, `PairLightPrepared26.data26SplitV1_leftCached_10`, `PairLightPrepared26.data26SplitV1_leftCached_11`, `PairLightPrepared26.leftCached`, `PairLightPrepared26.leftVertices`.
-- source:
--   D1Bound5/SmallPairLightData26.lean, lines 638-703, SHA-256 5846a48684f6c85575a6bcb6b11c73f695438e75f50a0505e9d333ffa48b497d; D1Bound5/SmallPairLightData26.lean, lines 705-770, SHA-256 5846a48684f6c85575a6bcb6b11c73f695438e75f50a0505e9d333ffa48b497d; D1Bound5/SmallPairLightData26.lean, lines 772-830, SHA-256 5846a48684f6c85575a6bcb6b11c73f695438e75f50a0505e9d333ffa48b497d; D1Bound5/SmallPairLightData26.lean, lines 832-832, SHA-256 5846a48684f6c85575a6bcb6b11c73f695438e75f50a0505e9d333ffa48b497d; D1Bound5/SmallPairLightData26.lean, lines 834-834, SHA-256 5846a48684f6c85575a6bcb6b11c73f695438e75f50a0505e9d333ffa48b497d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_106a2aa79285264daf8c
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_a8dd4fbf77f42cd70e3f
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_30f512df805a0b31d549
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_5d52387534451f627fb9
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_bca5494b5417cb004545
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_5ea323992cd49a0bd3d9
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_30fba6caa8b66805ecf9
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_a3f2f327c8fd90186dd1
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_d5def880f51e1202af42
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_002

section
namespace D1Bound5.PairLightPrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0





















private def data26SplitV1_leftCached_09 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_106a2aa79285264daf8c (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_a8dd4fbf77f42cd70e3f _root_.D1Bound5.Prove2MeTransfer.cachedSlice_30f512df805a0b31d549))

private def data26SplitV1_leftCached_10 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_5d52387534451f627fb9 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_bca5494b5417cb004545 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_5ea323992cd49a0bd3d9))

private def data26SplitV1_leftCached_11 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_30fba6caa8b66805ecf9 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_a3f2f327c8fd90186dd1 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_d5def880f51e1202af42))

def leftCached : List PairLightCachedVertex := List.append data26SplitV1_leftCached_00 (List.append data26SplitV1_leftCached_01 (List.append data26SplitV1_leftCached_02 (List.append data26SplitV1_leftCached_03 (List.append data26SplitV1_leftCached_04 (List.append data26SplitV1_leftCached_05 (List.append data26SplitV1_leftCached_06 (List.append data26SplitV1_leftCached_07 (List.append data26SplitV1_leftCached_08 (List.append data26SplitV1_leftCached_09 (List.append data26SplitV1_leftCached_10 (data26SplitV1_leftCached_11)))))))))))

def leftVertices : List PairLightCoordinate := leftCached.map Prod.fst

















































































end D1Bound5.PairLightPrepared26
end


