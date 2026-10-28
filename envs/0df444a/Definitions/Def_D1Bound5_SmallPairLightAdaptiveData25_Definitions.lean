-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData25_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:36:48.439654+00:00
-- url     : https://prove2.me/theorems/d3814647-eb88-43d5-a7b4-03195da92158
-- title:
--   Small Pair Light Adaptive Data25
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared25.leftCached000`, `PairLightAdaptivePrepared25.leftRows000`, `PairLightAdaptivePrepared25.leftCached001`, `PairLightAdaptivePrepared25.leftRows001`, `PairLightAdaptivePrepared25.leftCached002`, `PairLightAdaptivePrepared25.leftRows002`, `PairLightAdaptivePrepared25.rightCached000`, `PairLightAdaptivePrepared25.rightRows000` and 4 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData25.lean, lines 8-8, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669; D1Bound5/SmallPairLightAdaptiveData25.lean, lines 9-9, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669; D1Bound5/SmallPairLightAdaptiveData25.lean, lines 11-11, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669; D1Bound5/SmallPairLightAdaptiveData25.lean, lines 12-12, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669; D1Bound5/SmallPairLightAdaptiveData25.lean, lines 14-14, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669; D1Bound5/SmallPairLightAdaptiveData25.lean, lines 15-15, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669; D1Bound5/SmallPairLightAdaptiveData25.lean, lines 17-17, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669; D1Bound5/SmallPairLightAdaptiveData25.lean, lines 18-18, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669; D1Bound5/SmallPairLightAdaptiveData25.lean, lines 20-20, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669; D1Bound5/SmallPairLightAdaptiveData25.lean, lines 21-21, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669; D1Bound5/SmallPairLightAdaptiveData25.lean, lines 23-23, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669; D1Bound5/SmallPairLightAdaptiveData25.lean, lines 24-24, SHA-256 c7d4ac9f22e450b9eb02afc7c2048866bb44b40aa86b322ad9f1f05ec301d669. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData25Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData25Right_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared25.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared25.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 126
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 126

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 254
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 254

def rightCached000 : List PairLightCachedVertex := PairLightPrepared25.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared25.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 125
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 125

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 256
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 256


end D1Bound5.PairLightAdaptivePrepared25
end


