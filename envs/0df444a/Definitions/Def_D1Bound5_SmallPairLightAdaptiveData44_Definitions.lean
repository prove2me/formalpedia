-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData44_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData44_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:36:35.75471+00:00
-- url     : https://prove2.me/theorems/e932eb15-28ab-4762-99ed-7ce087d76a8b
-- title:
--   Small Pair Light Adaptive Data44
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared44.leftCached000`, `PairLightAdaptivePrepared44.leftRows000`, `PairLightAdaptivePrepared44.leftCached001`, `PairLightAdaptivePrepared44.leftRows001`, `PairLightAdaptivePrepared44.rightCached000`, `PairLightAdaptivePrepared44.rightRows000`, `PairLightAdaptivePrepared44.rightCached001`, `PairLightAdaptivePrepared44.rightRows001`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData44.lean, lines 8-8, SHA-256 e611ebe1be377f7eca9e38a25841a239590322bd850b902c822895e4a7da843e; D1Bound5/SmallPairLightAdaptiveData44.lean, lines 9-9, SHA-256 e611ebe1be377f7eca9e38a25841a239590322bd850b902c822895e4a7da843e; D1Bound5/SmallPairLightAdaptiveData44.lean, lines 11-11, SHA-256 e611ebe1be377f7eca9e38a25841a239590322bd850b902c822895e4a7da843e; D1Bound5/SmallPairLightAdaptiveData44.lean, lines 12-12, SHA-256 e611ebe1be377f7eca9e38a25841a239590322bd850b902c822895e4a7da843e; D1Bound5/SmallPairLightAdaptiveData44.lean, lines 14-14, SHA-256 e611ebe1be377f7eca9e38a25841a239590322bd850b902c822895e4a7da843e; D1Bound5/SmallPairLightAdaptiveData44.lean, lines 15-15, SHA-256 e611ebe1be377f7eca9e38a25841a239590322bd850b902c822895e4a7da843e; D1Bound5/SmallPairLightAdaptiveData44.lean, lines 17-17, SHA-256 e611ebe1be377f7eca9e38a25841a239590322bd850b902c822895e4a7da843e; D1Bound5/SmallPairLightAdaptiveData44.lean, lines 18-18, SHA-256 e611ebe1be377f7eca9e38a25841a239590322bd850b902c822895e4a7da843e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared44.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared44.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 220
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 220

def rightCached000 : List PairLightCachedVertex := PairLightPrepared44.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared44.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 220
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 220


end D1Bound5.PairLightAdaptivePrepared44
end


