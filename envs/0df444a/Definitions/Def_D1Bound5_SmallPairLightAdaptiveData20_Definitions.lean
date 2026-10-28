-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData20_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData20_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:38:43.965282+00:00
-- url     : https://prove2.me/theorems/036215ff-bde0-4436-8860-55d850330545
-- title:
--   Small Pair Light Adaptive Data20
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared20.leftCached000`, `PairLightAdaptivePrepared20.leftRows000`, `PairLightAdaptivePrepared20.leftCached001`, `PairLightAdaptivePrepared20.leftRows001`, `PairLightAdaptivePrepared20.rightCached000`, `PairLightAdaptivePrepared20.rightRows000`, `PairLightAdaptivePrepared20.rightCached001`, `PairLightAdaptivePrepared20.rightRows001`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData20.lean, lines 8-8, SHA-256 92b900ee0f842d01f9e4db6cbd254162f506b2c67278435a0a53a8d704f9afc1; D1Bound5/SmallPairLightAdaptiveData20.lean, lines 9-9, SHA-256 92b900ee0f842d01f9e4db6cbd254162f506b2c67278435a0a53a8d704f9afc1; D1Bound5/SmallPairLightAdaptiveData20.lean, lines 11-11, SHA-256 92b900ee0f842d01f9e4db6cbd254162f506b2c67278435a0a53a8d704f9afc1; D1Bound5/SmallPairLightAdaptiveData20.lean, lines 12-12, SHA-256 92b900ee0f842d01f9e4db6cbd254162f506b2c67278435a0a53a8d704f9afc1; D1Bound5/SmallPairLightAdaptiveData20.lean, lines 14-14, SHA-256 92b900ee0f842d01f9e4db6cbd254162f506b2c67278435a0a53a8d704f9afc1; D1Bound5/SmallPairLightAdaptiveData20.lean, lines 15-15, SHA-256 92b900ee0f842d01f9e4db6cbd254162f506b2c67278435a0a53a8d704f9afc1; D1Bound5/SmallPairLightAdaptiveData20.lean, lines 17-17, SHA-256 92b900ee0f842d01f9e4db6cbd254162f506b2c67278435a0a53a8d704f9afc1; D1Bound5/SmallPairLightAdaptiveData20.lean, lines 18-18, SHA-256 92b900ee0f842d01f9e4db6cbd254162f506b2c67278435a0a53a8d704f9afc1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared20.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared20.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 223
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 223

def rightCached000 : List PairLightCachedVertex := PairLightPrepared20.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared20.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 223
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 223


end D1Bound5.PairLightAdaptivePrepared20
end


