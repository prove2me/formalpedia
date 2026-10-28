-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData43_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData43_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:41:09.383842+00:00
-- url     : https://prove2.me/theorems/cfd7bd54-b023-4663-85d1-5cf4e822ebb2
-- title:
--   Small Pair Light Adaptive Data43
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared43.leftCached000`, `PairLightAdaptivePrepared43.leftRows000`, `PairLightAdaptivePrepared43.leftCached001`, `PairLightAdaptivePrepared43.leftRows001`, `PairLightAdaptivePrepared43.leftCached002`, `PairLightAdaptivePrepared43.leftRows002`, `PairLightAdaptivePrepared43.leftCached003`, `PairLightAdaptivePrepared43.leftRows003` and 8 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData43.lean, lines 8-8, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 9-9, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 11-11, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 12-12, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 14-14, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 15-15, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 17-17, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 18-18, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 20-20, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 21-21, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 23-23, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 24-24, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 26-26, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 27-27, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 29-29, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d; D1Bound5/SmallPairLightAdaptiveData43.lean, lines 30-30, SHA-256 917ddcd6366a27d39c68ebedf31c878a4e699ed35bc8b4827b3f787eb104880d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared43.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared43.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 91
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 91

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 121
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 121

def leftCached003 : List PairLightCachedVertex := leftCached002.drop 270
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 270

def rightCached000 : List PairLightCachedVertex := PairLightPrepared43.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared43.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 92
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 92

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 122
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 122

def rightCached003 : List PairLightCachedVertex := rightCached002.drop 266
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 266


end D1Bound5.PairLightAdaptivePrepared43
end


