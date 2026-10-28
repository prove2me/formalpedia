-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData4RightCachedChunk05_Definitions
-- name    : D1Bound5_SmallPairLightData4RightCachedChunk05_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:41:52.336755+00:00
-- url     : https://prove2.me/theorems/5050117a-d3cb-4614-9931-b9e47ff621d8
-- title:
--   Small Pair Light Data4Right Cached Chunk05
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared4.rightCachedChunk05`.
-- source:
--   D1Bound5/SmallPairLightData4RightCachedChunk05.lean, lines 9-106, SHA-256 1a5284d2e16df74787bfd650471d1df764b59d7141628118ed606fe3243bd0b2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_edccc15259d6e59940c6
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_22fd4a03a641ccb798b7
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_70ff3f0c2f68c78db114
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_166167679fe69fa8fb6f
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


noncomputable def rightCachedChunk05 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_edccc15259d6e59940c6 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_22fd4a03a641ccb798b7 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_70ff3f0c2f68c78db114 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_166167679fe69fa8fb6f)))

end D1Bound5.PairLightPrepared4
end


