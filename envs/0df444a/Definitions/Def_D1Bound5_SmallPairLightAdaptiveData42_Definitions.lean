-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData42_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData42_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:36:52.914729+00:00
-- url     : https://prove2.me/theorems/af4f0ffc-1f7a-49b7-96ec-5df835565986
-- title:
--   Small Pair Light Adaptive Data42
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared42.leftCached000`, `PairLightAdaptivePrepared42.leftRows000`, `PairLightAdaptivePrepared42.leftCached001`, `PairLightAdaptivePrepared42.leftRows001`, `PairLightAdaptivePrepared42.rightCached000`, `PairLightAdaptivePrepared42.rightRows000`, `PairLightAdaptivePrepared42.rightCached001`, `PairLightAdaptivePrepared42.rightRows001`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData42.lean, lines 8-8, SHA-256 ebf8c5a2c64b19bd6d5c76c20ca766b5a849c0eea3d7895f143e4cf28cd0ac4d; D1Bound5/SmallPairLightAdaptiveData42.lean, lines 9-9, SHA-256 ebf8c5a2c64b19bd6d5c76c20ca766b5a849c0eea3d7895f143e4cf28cd0ac4d; D1Bound5/SmallPairLightAdaptiveData42.lean, lines 11-11, SHA-256 ebf8c5a2c64b19bd6d5c76c20ca766b5a849c0eea3d7895f143e4cf28cd0ac4d; D1Bound5/SmallPairLightAdaptiveData42.lean, lines 12-12, SHA-256 ebf8c5a2c64b19bd6d5c76c20ca766b5a849c0eea3d7895f143e4cf28cd0ac4d; D1Bound5/SmallPairLightAdaptiveData42.lean, lines 14-14, SHA-256 ebf8c5a2c64b19bd6d5c76c20ca766b5a849c0eea3d7895f143e4cf28cd0ac4d; D1Bound5/SmallPairLightAdaptiveData42.lean, lines 15-15, SHA-256 ebf8c5a2c64b19bd6d5c76c20ca766b5a849c0eea3d7895f143e4cf28cd0ac4d; D1Bound5/SmallPairLightAdaptiveData42.lean, lines 17-17, SHA-256 ebf8c5a2c64b19bd6d5c76c20ca766b5a849c0eea3d7895f143e4cf28cd0ac4d; D1Bound5/SmallPairLightAdaptiveData42.lean, lines 18-18, SHA-256 ebf8c5a2c64b19bd6d5c76c20ca766b5a849c0eea3d7895f143e4cf28cd0ac4d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared42.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared42.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 242
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 242

def rightCached000 : List PairLightCachedVertex := PairLightPrepared42.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared42.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 242
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 242


end D1Bound5.PairLightAdaptivePrepared42
end


