-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData45_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData45_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:38:32.890528+00:00
-- url     : https://prove2.me/theorems/bb907076-5e74-4491-b3c1-4237d2cb0230
-- title:
--   Small Pair Light Adaptive Data45
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared45.leftCached000`, `PairLightAdaptivePrepared45.leftRows000`, `PairLightAdaptivePrepared45.leftCached001`, `PairLightAdaptivePrepared45.leftRows001`, `PairLightAdaptivePrepared45.leftCached002`, `PairLightAdaptivePrepared45.leftRows002`, `PairLightAdaptivePrepared45.leftCached003`, `PairLightAdaptivePrepared45.leftRows003` and 8 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData45.lean, lines 8-8, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 9-9, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 11-11, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 12-12, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 14-14, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 15-15, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 17-17, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 18-18, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 20-20, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 21-21, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 23-23, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 24-24, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 26-26, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 27-27, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 29-29, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d; D1Bound5/SmallPairLightAdaptiveData45.lean, lines 30-30, SHA-256 40cb07fc08585b72cf1433ef04afbfacced74280d6fa87b8af1c016066d50f3d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared45.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared45.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 43
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 43

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 61
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 61

def leftCached003 : List PairLightCachedVertex := leftCached002.drop 101
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 101

def rightCached000 : List PairLightCachedVertex := PairLightPrepared45.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared45.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 43
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 43

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 60
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 60

def rightCached003 : List PairLightCachedVertex := rightCached002.drop 103
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 103


end D1Bound5.PairLightAdaptivePrepared45
end


