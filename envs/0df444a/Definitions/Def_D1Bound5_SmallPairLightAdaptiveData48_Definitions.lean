-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData48_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:36:48.557812+00:00
-- url     : https://prove2.me/theorems/56d9f71d-2a11-4e09-a62b-fb43c662b58b
-- title:
--   Small Pair Light Adaptive Data48
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared48.leftCached000`, `PairLightAdaptivePrepared48.leftRows000`, `PairLightAdaptivePrepared48.leftCached001`, `PairLightAdaptivePrepared48.leftRows001`, `PairLightAdaptivePrepared48.leftCached002`, `PairLightAdaptivePrepared48.leftRows002`, `PairLightAdaptivePrepared48.rightCached000`, `PairLightAdaptivePrepared48.rightRows000` and 4 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData48.lean, lines 8-8, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc; D1Bound5/SmallPairLightAdaptiveData48.lean, lines 9-9, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc; D1Bound5/SmallPairLightAdaptiveData48.lean, lines 11-11, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc; D1Bound5/SmallPairLightAdaptiveData48.lean, lines 12-12, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc; D1Bound5/SmallPairLightAdaptiveData48.lean, lines 14-14, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc; D1Bound5/SmallPairLightAdaptiveData48.lean, lines 15-15, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc; D1Bound5/SmallPairLightAdaptiveData48.lean, lines 17-17, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc; D1Bound5/SmallPairLightAdaptiveData48.lean, lines 18-18, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc; D1Bound5/SmallPairLightAdaptiveData48.lean, lines 20-20, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc; D1Bound5/SmallPairLightAdaptiveData48.lean, lines 21-21, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc; D1Bound5/SmallPairLightAdaptiveData48.lean, lines 23-23, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc; D1Bound5/SmallPairLightAdaptiveData48.lean, lines 24-24, SHA-256 b79f464eb54ae3298effb46323160997915f8580a3403b81d90087cf25e694dc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData48Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData48Right_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared48.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared48.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 137
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 137

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 223
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 223

def rightCached000 : List PairLightCachedVertex := PairLightPrepared48.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared48.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 138
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 138

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 220
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 220


end D1Bound5.PairLightAdaptivePrepared48
end


