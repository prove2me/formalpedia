-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData12_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:36:58.914991+00:00
-- url     : https://prove2.me/theorems/2b092bbb-e38e-4e27-9849-d58bccd9ce34
-- title:
--   Small Pair Light Adaptive Data12
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared12.leftCached000`, `PairLightAdaptivePrepared12.leftRows000`, `PairLightAdaptivePrepared12.leftCached001`, `PairLightAdaptivePrepared12.leftRows001`, `PairLightAdaptivePrepared12.leftCached002`, `PairLightAdaptivePrepared12.leftRows002`, `PairLightAdaptivePrepared12.rightCached000`, `PairLightAdaptivePrepared12.rightRows000` and 4 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData12.lean, lines 8-8, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec; D1Bound5/SmallPairLightAdaptiveData12.lean, lines 9-9, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec; D1Bound5/SmallPairLightAdaptiveData12.lean, lines 11-11, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec; D1Bound5/SmallPairLightAdaptiveData12.lean, lines 12-12, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec; D1Bound5/SmallPairLightAdaptiveData12.lean, lines 14-14, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec; D1Bound5/SmallPairLightAdaptiveData12.lean, lines 15-15, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec; D1Bound5/SmallPairLightAdaptiveData12.lean, lines 17-17, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec; D1Bound5/SmallPairLightAdaptiveData12.lean, lines 18-18, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec; D1Bound5/SmallPairLightAdaptiveData12.lean, lines 20-20, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec; D1Bound5/SmallPairLightAdaptiveData12.lean, lines 21-21, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec; D1Bound5/SmallPairLightAdaptiveData12.lean, lines 23-23, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec; D1Bound5/SmallPairLightAdaptiveData12.lean, lines 24-24, SHA-256 fe326f418d084d8979551f09d016c1a3df0087271ef919a8cd3db45a9e35acec. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_005
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_006

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared12.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared12.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 138
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 138

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 221
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 221

def rightCached000 : List PairLightCachedVertex := PairLightPrepared12.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared12.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 138
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 138

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 221
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 221


end D1Bound5.PairLightAdaptivePrepared12
end


