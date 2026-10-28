-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData7_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData7_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:36:44.92255+00:00
-- url     : https://prove2.me/theorems/f8d70259-2935-47fc-8c59-546e767c2232
-- title:
--   Small Pair Light Adaptive Data7
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared7.leftCached000`, `PairLightAdaptivePrepared7.leftRows000`, `PairLightAdaptivePrepared7.leftCached001`, `PairLightAdaptivePrepared7.leftRows001`, `PairLightAdaptivePrepared7.leftCached002`, `PairLightAdaptivePrepared7.leftRows002`, `PairLightAdaptivePrepared7.leftCached003`, `PairLightAdaptivePrepared7.leftRows003` and 8 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData7.lean, lines 8-8, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 9-9, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 11-11, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 12-12, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 14-14, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 15-15, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 17-17, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 18-18, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 20-20, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 21-21, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 23-23, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 24-24, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 26-26, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 27-27, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 29-29, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309; D1Bound5/SmallPairLightAdaptiveData7.lean, lines 30-30, SHA-256 ec327ff46b1c46c8f3ee5f5ad525df0183373497a9a930244cfdbb9b763b5309. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared7.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared7.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 105
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 105

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 163
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 163

def leftCached003 : List PairLightCachedVertex := leftCached002.drop 164
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 164

def rightCached000 : List PairLightCachedVertex := PairLightPrepared7.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared7.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 106
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 106

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 166
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 166

def rightCached003 : List PairLightCachedVertex := rightCached002.drop 158
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 158


end D1Bound5.PairLightAdaptivePrepared7
end


