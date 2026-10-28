-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData40_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:41:21.784354+00:00
-- url     : https://prove2.me/theorems/8c948071-ba79-47e9-9eb7-cb31f38bfaf2
-- title:
--   Small Pair Light Adaptive Data40
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared40.leftCached000`, `PairLightAdaptivePrepared40.leftRows000`, `PairLightAdaptivePrepared40.leftCached001`, `PairLightAdaptivePrepared40.leftRows001`, `PairLightAdaptivePrepared40.leftCached002`, `PairLightAdaptivePrepared40.leftRows002`, `PairLightAdaptivePrepared40.rightCached000`, `PairLightAdaptivePrepared40.rightRows000` and 4 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData40.lean, lines 8-8, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7; D1Bound5/SmallPairLightAdaptiveData40.lean, lines 9-9, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7; D1Bound5/SmallPairLightAdaptiveData40.lean, lines 11-11, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7; D1Bound5/SmallPairLightAdaptiveData40.lean, lines 12-12, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7; D1Bound5/SmallPairLightAdaptiveData40.lean, lines 14-14, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7; D1Bound5/SmallPairLightAdaptiveData40.lean, lines 15-15, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7; D1Bound5/SmallPairLightAdaptiveData40.lean, lines 17-17, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7; D1Bound5/SmallPairLightAdaptiveData40.lean, lines 18-18, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7; D1Bound5/SmallPairLightAdaptiveData40.lean, lines 20-20, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7; D1Bound5/SmallPairLightAdaptiveData40.lean, lines 21-21, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7; D1Bound5/SmallPairLightAdaptiveData40.lean, lines 23-23, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7; D1Bound5/SmallPairLightAdaptiveData40.lean, lines 24-24, SHA-256 df692ff346963e3126768090cdeeb41cc35273d77054111d9a221ba42dc254c7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_005

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared40.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared40.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 137
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 137

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 223
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 223

def rightCached000 : List PairLightCachedVertex := PairLightPrepared40.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared40.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 138
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 138

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 220
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 220


end D1Bound5.PairLightAdaptivePrepared40
end


