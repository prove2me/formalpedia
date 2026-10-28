-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData9_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData9_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T03:22:32.922851+00:00
-- url     : https://prove2.me/theorems/e77da13b-3a1b-4b8c-9056-b2cb733f0c75
-- title:
--   Small Pair Light Adaptive Data9
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared9.leftCached000`, `PairLightAdaptivePrepared9.leftRows000`, `PairLightAdaptivePrepared9.leftCached001`, `PairLightAdaptivePrepared9.leftRows001`, `PairLightAdaptivePrepared9.rightCached000`, `PairLightAdaptivePrepared9.rightRows000`, `PairLightAdaptivePrepared9.rightCached001`, `PairLightAdaptivePrepared9.rightRows001`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData9.lean, lines 8-8, SHA-256 ecba11303c47cffbba9f79d83b18960fdf6872666df52288a4456d8cbc6da481; D1Bound5/SmallPairLightAdaptiveData9.lean, lines 9-9, SHA-256 ecba11303c47cffbba9f79d83b18960fdf6872666df52288a4456d8cbc6da481; D1Bound5/SmallPairLightAdaptiveData9.lean, lines 11-11, SHA-256 ecba11303c47cffbba9f79d83b18960fdf6872666df52288a4456d8cbc6da481; D1Bound5/SmallPairLightAdaptiveData9.lean, lines 12-12, SHA-256 ecba11303c47cffbba9f79d83b18960fdf6872666df52288a4456d8cbc6da481; D1Bound5/SmallPairLightAdaptiveData9.lean, lines 14-14, SHA-256 ecba11303c47cffbba9f79d83b18960fdf6872666df52288a4456d8cbc6da481; D1Bound5/SmallPairLightAdaptiveData9.lean, lines 15-15, SHA-256 ecba11303c47cffbba9f79d83b18960fdf6872666df52288a4456d8cbc6da481; D1Bound5/SmallPairLightAdaptiveData9.lean, lines 17-17, SHA-256 ecba11303c47cffbba9f79d83b18960fdf6872666df52288a4456d8cbc6da481; D1Bound5/SmallPairLightAdaptiveData9.lean, lines 18-18, SHA-256 ecba11303c47cffbba9f79d83b18960fdf6872666df52288a4456d8cbc6da481. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared9.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared9.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 219
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 219

def rightCached000 : List PairLightCachedVertex := PairLightPrepared9.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared9.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 219
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 219


end D1Bound5.PairLightAdaptivePrepared9
end


