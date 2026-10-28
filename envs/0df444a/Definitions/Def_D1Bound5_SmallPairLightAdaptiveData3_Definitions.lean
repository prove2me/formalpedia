-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData3_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData3_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:36:29.169993+00:00
-- url     : https://prove2.me/theorems/00084e09-f598-4e05-8f6a-0468bd7eaf1a
-- title:
--   Small Pair Light Adaptive Data3
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared3.leftCached000`, `PairLightAdaptivePrepared3.leftRows000`, `PairLightAdaptivePrepared3.leftCached001`, `PairLightAdaptivePrepared3.leftRows001`, `PairLightAdaptivePrepared3.leftCached002`, `PairLightAdaptivePrepared3.leftRows002`, `PairLightAdaptivePrepared3.leftCached003`, `PairLightAdaptivePrepared3.leftRows003` and 8 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData3.lean, lines 8-8, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 9-9, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 11-11, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 12-12, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 14-14, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 15-15, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 17-17, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 18-18, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 20-20, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 21-21, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 23-23, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 24-24, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 26-26, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 27-27, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 29-29, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513; D1Bound5/SmallPairLightAdaptiveData3.lean, lines 30-30, SHA-256 f635cd4589d05fd53757fd49742c4d64e07139e743849150d36bb1a4c8ddc513. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared3.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared3.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 112
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 112

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 199
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 199

def leftCached003 : List PairLightCachedVertex := leftCached002.drop 102
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 102

def rightCached000 : List PairLightCachedVertex := PairLightPrepared3.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared3.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 111
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 111

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 195
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 195

def rightCached003 : List PairLightCachedVertex := rightCached002.drop 108
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 108


end D1Bound5.PairLightAdaptivePrepared3
end


