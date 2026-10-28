-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData8RightCachedChunk02_Definitions
-- name    : D1Bound5_SmallPairLightData8RightCachedChunk02_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:45:15.566897+00:00
-- url     : https://prove2.me/theorems/3b820950-b728-4307-891e-0c35eec150c4
-- title:
--   Small Pair Light Data8Right Cached Chunk02
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared8.rightCachedChunk02`.
-- source:
--   D1Bound5/SmallPairLightData8RightCachedChunk02.lean, lines 8-109, SHA-256 07a6b712f6d84eb5acf252428fccaebf7f2257dab466a306a2203bc6e6426e2e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_3bb3d7775f8977d76aed
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_2ae404cab298985c1dc4
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_32a8175ce60c604d87f5
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_80d68179849394f46fe7
import Definitions.Def_D1Bound5_Prove2MeTransfer_cachedSlice_863b274e49b46480cab7
import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5.PairLightPrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightCachedChunk02 : List PairLightCachedVertex := (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_3bb3d7775f8977d76aed (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_2ae404cab298985c1dc4 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_32a8175ce60c604d87f5 (_root_.List.append _root_.D1Bound5.Prove2MeTransfer.cachedSlice_80d68179849394f46fe7 _root_.D1Bound5.Prove2MeTransfer.cachedSlice_863b274e49b46480cab7))))

end D1Bound5.PairLightPrepared8
end


