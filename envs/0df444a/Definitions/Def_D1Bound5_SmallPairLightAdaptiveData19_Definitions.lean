-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData19_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData19_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:39:10.769909+00:00
-- url     : https://prove2.me/theorems/884a27cb-c4ba-4b1c-b3dd-3b552dfcc25a
-- title:
--   Small Pair Light Adaptive Data19
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared19.leftCached000`, `PairLightAdaptivePrepared19.leftRows000`, `PairLightAdaptivePrepared19.leftCached001`, `PairLightAdaptivePrepared19.leftRows001`, `PairLightAdaptivePrepared19.leftCached002`, `PairLightAdaptivePrepared19.leftRows002`, `PairLightAdaptivePrepared19.leftCached003`, `PairLightAdaptivePrepared19.leftRows003` and 8 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData19.lean, lines 8-8, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 9-9, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 11-11, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 12-12, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 14-14, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 15-15, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 17-17, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 18-18, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 20-20, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 21-21, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 23-23, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 24-24, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 26-26, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 27-27, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 29-29, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670; D1Bound5/SmallPairLightAdaptiveData19.lean, lines 30-30, SHA-256 8297a1256676869c9137b5f998d58457d9f86fbf1c4b0a32de58b35c04807670. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared19.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared19.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 101
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 101

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 147
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 147

def leftCached003 : List PairLightCachedVertex := leftCached002.drop 198
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 198

def rightCached000 : List PairLightCachedVertex := PairLightPrepared19.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared19.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 101
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 101

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 147
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 147

def rightCached003 : List PairLightCachedVertex := rightCached002.drop 198
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 198


end D1Bound5.PairLightAdaptivePrepared19
end


