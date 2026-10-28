-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData46_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:43:52.409066+00:00
-- url     : https://prove2.me/theorems/0ec753c7-a9cc-4144-afb3-95ccc620dd8a
-- title:
--   Small Pair Light Adaptive Data46
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared46.leftCached000`, `PairLightAdaptivePrepared46.leftRows000`, `PairLightAdaptivePrepared46.leftCached001`, `PairLightAdaptivePrepared46.leftRows001`, `PairLightAdaptivePrepared46.leftCached002`, `PairLightAdaptivePrepared46.leftRows002`, `PairLightAdaptivePrepared46.rightCached000`, `PairLightAdaptivePrepared46.rightRows000` and 4 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData46.lean, lines 8-8, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d; D1Bound5/SmallPairLightAdaptiveData46.lean, lines 9-9, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d; D1Bound5/SmallPairLightAdaptiveData46.lean, lines 11-11, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d; D1Bound5/SmallPairLightAdaptiveData46.lean, lines 12-12, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d; D1Bound5/SmallPairLightAdaptiveData46.lean, lines 14-14, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d; D1Bound5/SmallPairLightAdaptiveData46.lean, lines 15-15, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d; D1Bound5/SmallPairLightAdaptiveData46.lean, lines 17-17, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d; D1Bound5/SmallPairLightAdaptiveData46.lean, lines 18-18, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d; D1Bound5/SmallPairLightAdaptiveData46.lean, lines 20-20, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d; D1Bound5/SmallPairLightAdaptiveData46.lean, lines 21-21, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d; D1Bound5/SmallPairLightAdaptiveData46.lean, lines 23-23, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d; D1Bound5/SmallPairLightAdaptiveData46.lean, lines 24-24, SHA-256 18f080c0c7e29d88ea48f60a5cbee00f8cad2147bed5cdd93dc7f451fb8bfc4d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData46RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared46.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared46.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 137
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 137

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 223
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 223

def rightCached000 : List PairLightCachedVertex := PairLightPrepared46.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared46.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 138
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 138

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 220
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 220


end D1Bound5.PairLightAdaptivePrepared46
end


