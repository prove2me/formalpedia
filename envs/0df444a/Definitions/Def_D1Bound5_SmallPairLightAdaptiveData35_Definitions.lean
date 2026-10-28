-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData35_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:34:09.672819+00:00
-- url     : https://prove2.me/theorems/47e41e32-441b-4972-a902-197e80a87620
-- title:
--   Small Pair Light Adaptive Data35
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared35.leftCached000`, `PairLightAdaptivePrepared35.leftRows000`, `PairLightAdaptivePrepared35.leftCached001`, `PairLightAdaptivePrepared35.leftRows001`, `PairLightAdaptivePrepared35.leftCached002`, `PairLightAdaptivePrepared35.leftRows002`, `PairLightAdaptivePrepared35.rightCached000`, `PairLightAdaptivePrepared35.rightRows000` and 4 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData35.lean, lines 8-8, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7; D1Bound5/SmallPairLightAdaptiveData35.lean, lines 9-9, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7; D1Bound5/SmallPairLightAdaptiveData35.lean, lines 11-11, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7; D1Bound5/SmallPairLightAdaptiveData35.lean, lines 12-12, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7; D1Bound5/SmallPairLightAdaptiveData35.lean, lines 14-14, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7; D1Bound5/SmallPairLightAdaptiveData35.lean, lines 15-15, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7; D1Bound5/SmallPairLightAdaptiveData35.lean, lines 17-17, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7; D1Bound5/SmallPairLightAdaptiveData35.lean, lines 18-18, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7; D1Bound5/SmallPairLightAdaptiveData35.lean, lines 20-20, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7; D1Bound5/SmallPairLightAdaptiveData35.lean, lines 21-21, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7; D1Bound5/SmallPairLightAdaptiveData35.lean, lines 23-23, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7; D1Bound5/SmallPairLightAdaptiveData35.lean, lines 24-24, SHA-256 24623924ad84f45539421e8e4e0212dee586f0f9acc467bf65cc90d84ce4a7f7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData35Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData35Right_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared35.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared35.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 132
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 132

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 237
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 237

def rightCached000 : List PairLightCachedVertex := PairLightPrepared35.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared35.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 132
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 132

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 236
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 236


end D1Bound5.PairLightAdaptivePrepared35
end


