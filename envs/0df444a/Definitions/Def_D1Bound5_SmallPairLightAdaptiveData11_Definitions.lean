-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData11_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:37:47.22698+00:00
-- url     : https://prove2.me/theorems/fddbff1a-f022-4030-b81b-f26727cd9f1b
-- title:
--   Small Pair Light Adaptive Data11
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared11.leftCached000`, `PairLightAdaptivePrepared11.leftRows000`, `PairLightAdaptivePrepared11.leftCached001`, `PairLightAdaptivePrepared11.leftRows001`, `PairLightAdaptivePrepared11.leftCached002`, `PairLightAdaptivePrepared11.leftRows002`, `PairLightAdaptivePrepared11.rightCached000`, `PairLightAdaptivePrepared11.rightRows000` and 4 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData11.lean, lines 8-8, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0; D1Bound5/SmallPairLightAdaptiveData11.lean, lines 9-9, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0; D1Bound5/SmallPairLightAdaptiveData11.lean, lines 11-11, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0; D1Bound5/SmallPairLightAdaptiveData11.lean, lines 12-12, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0; D1Bound5/SmallPairLightAdaptiveData11.lean, lines 14-14, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0; D1Bound5/SmallPairLightAdaptiveData11.lean, lines 15-15, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0; D1Bound5/SmallPairLightAdaptiveData11.lean, lines 17-17, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0; D1Bound5/SmallPairLightAdaptiveData11.lean, lines 18-18, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0; D1Bound5/SmallPairLightAdaptiveData11.lean, lines 20-20, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0; D1Bound5/SmallPairLightAdaptiveData11.lean, lines 21-21, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0; D1Bound5/SmallPairLightAdaptiveData11.lean, lines 23-23, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0; D1Bound5/SmallPairLightAdaptiveData11.lean, lines 24-24, SHA-256 e363601e1f8ad8d058fee259a0b6e71200da85795a9b06a7bac76285671940e0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData11RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared11.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared11.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 138
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 138

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 221
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 221

def rightCached000 : List PairLightCachedVertex := PairLightPrepared11.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared11.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 138
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 138

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 221
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 221


end D1Bound5.PairLightAdaptivePrepared11
end


