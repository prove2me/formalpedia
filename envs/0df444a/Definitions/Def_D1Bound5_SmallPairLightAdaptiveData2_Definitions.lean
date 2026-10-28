-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData2_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData2_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:39:08.760325+00:00
-- url     : https://prove2.me/theorems/555d0b58-f54f-4dfa-b609-0ec0a419017f
-- title:
--   Small Pair Light Adaptive Data2
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared2.leftCached000`, `PairLightAdaptivePrepared2.leftRows000`, `PairLightAdaptivePrepared2.leftCached001`, `PairLightAdaptivePrepared2.leftRows001`, `PairLightAdaptivePrepared2.rightCached000`, `PairLightAdaptivePrepared2.rightRows000`, `PairLightAdaptivePrepared2.rightCached001`, `PairLightAdaptivePrepared2.rightRows001`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData2.lean, lines 8-8, SHA-256 6681d4c424e9771baf7a799da4dd847dca8cff853a1b251ca91cc50e2a161d75; D1Bound5/SmallPairLightAdaptiveData2.lean, lines 9-9, SHA-256 6681d4c424e9771baf7a799da4dd847dca8cff853a1b251ca91cc50e2a161d75; D1Bound5/SmallPairLightAdaptiveData2.lean, lines 11-11, SHA-256 6681d4c424e9771baf7a799da4dd847dca8cff853a1b251ca91cc50e2a161d75; D1Bound5/SmallPairLightAdaptiveData2.lean, lines 12-12, SHA-256 6681d4c424e9771baf7a799da4dd847dca8cff853a1b251ca91cc50e2a161d75; D1Bound5/SmallPairLightAdaptiveData2.lean, lines 14-14, SHA-256 6681d4c424e9771baf7a799da4dd847dca8cff853a1b251ca91cc50e2a161d75; D1Bound5/SmallPairLightAdaptiveData2.lean, lines 15-15, SHA-256 6681d4c424e9771baf7a799da4dd847dca8cff853a1b251ca91cc50e2a161d75; D1Bound5/SmallPairLightAdaptiveData2.lean, lines 17-17, SHA-256 6681d4c424e9771baf7a799da4dd847dca8cff853a1b251ca91cc50e2a161d75; D1Bound5/SmallPairLightAdaptiveData2.lean, lines 18-18, SHA-256 6681d4c424e9771baf7a799da4dd847dca8cff853a1b251ca91cc50e2a161d75. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared2.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared2.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 207
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 207

def rightCached000 : List PairLightCachedVertex := PairLightPrepared2.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared2.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 207
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 207


end D1Bound5.PairLightAdaptivePrepared2
end


