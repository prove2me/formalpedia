-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData29_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:37:17.509081+00:00
-- url     : https://prove2.me/theorems/58a9c0f3-0a63-4b3c-b6b5-d0e6579ee413
-- title:
--   Small Pair Light Adaptive Data29
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared29.leftCached000`, `PairLightAdaptivePrepared29.leftRows000`, `PairLightAdaptivePrepared29.leftCached001`, `PairLightAdaptivePrepared29.leftRows001`, `PairLightAdaptivePrepared29.leftCached002`, `PairLightAdaptivePrepared29.leftRows002`, `PairLightAdaptivePrepared29.rightCached000`, `PairLightAdaptivePrepared29.rightRows000` and 4 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData29.lean, lines 8-8, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556; D1Bound5/SmallPairLightAdaptiveData29.lean, lines 9-9, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556; D1Bound5/SmallPairLightAdaptiveData29.lean, lines 11-11, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556; D1Bound5/SmallPairLightAdaptiveData29.lean, lines 12-12, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556; D1Bound5/SmallPairLightAdaptiveData29.lean, lines 14-14, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556; D1Bound5/SmallPairLightAdaptiveData29.lean, lines 15-15, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556; D1Bound5/SmallPairLightAdaptiveData29.lean, lines 17-17, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556; D1Bound5/SmallPairLightAdaptiveData29.lean, lines 18-18, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556; D1Bound5/SmallPairLightAdaptiveData29.lean, lines 20-20, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556; D1Bound5/SmallPairLightAdaptiveData29.lean, lines 21-21, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556; D1Bound5/SmallPairLightAdaptiveData29.lean, lines 23-23, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556; D1Bound5/SmallPairLightAdaptiveData29.lean, lines 24-24, SHA-256 1dd0a18b0536efc473acae96568e73d9a51f07edc453738e5cd23e2e37d4a556. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared29.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared29.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 126
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 126

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 254
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 254

def rightCached000 : List PairLightCachedVertex := PairLightPrepared29.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared29.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 125
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 125

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 256
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 256


end D1Bound5.PairLightAdaptivePrepared29
end


