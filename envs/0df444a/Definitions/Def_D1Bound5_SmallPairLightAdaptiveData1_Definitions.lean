-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData1_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:34:34.515274+00:00
-- url     : https://prove2.me/theorems/7dd3f408-1960-4961-80df-aecc24635139
-- title:
--   Small Pair Light Adaptive Data1
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared1.leftCached000`, `PairLightAdaptivePrepared1.leftRows000`, `PairLightAdaptivePrepared1.leftCached001`, `PairLightAdaptivePrepared1.leftRows001`, `PairLightAdaptivePrepared1.leftCached002`, `PairLightAdaptivePrepared1.leftRows002`, `PairLightAdaptivePrepared1.rightCached000`, `PairLightAdaptivePrepared1.rightRows000` and 4 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData1.lean, lines 8-8, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4; D1Bound5/SmallPairLightAdaptiveData1.lean, lines 9-9, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4; D1Bound5/SmallPairLightAdaptiveData1.lean, lines 11-11, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4; D1Bound5/SmallPairLightAdaptiveData1.lean, lines 12-12, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4; D1Bound5/SmallPairLightAdaptiveData1.lean, lines 14-14, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4; D1Bound5/SmallPairLightAdaptiveData1.lean, lines 15-15, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4; D1Bound5/SmallPairLightAdaptiveData1.lean, lines 17-17, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4; D1Bound5/SmallPairLightAdaptiveData1.lean, lines 18-18, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4; D1Bound5/SmallPairLightAdaptiveData1.lean, lines 20-20, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4; D1Bound5/SmallPairLightAdaptiveData1.lean, lines 21-21, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4; D1Bound5/SmallPairLightAdaptiveData1.lean, lines 23-23, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4; D1Bound5/SmallPairLightAdaptiveData1.lean, lines 24-24, SHA-256 023209fa7e5c3eda67ab9cb0a61a406f496298e974a7a1a28f5119f332e43ae4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData1RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared1.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared1.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 137
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 137

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 223
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 223

def rightCached000 : List PairLightCachedVertex := PairLightPrepared1.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared1.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 138
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 138

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 220
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 220


end D1Bound5.PairLightAdaptivePrepared1
end


