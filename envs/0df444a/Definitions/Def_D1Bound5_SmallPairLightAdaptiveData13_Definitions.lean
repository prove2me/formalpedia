-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData13_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData13_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:41:13.858984+00:00
-- url     : https://prove2.me/theorems/7e53d098-7a33-4d63-a02e-7f19cf0d9a9d
-- title:
--   Small Pair Light Adaptive Data13
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared13.leftCached000`, `PairLightAdaptivePrepared13.leftRows000`, `PairLightAdaptivePrepared13.leftCached001`, `PairLightAdaptivePrepared13.leftRows001`, `PairLightAdaptivePrepared13.rightCached000`, `PairLightAdaptivePrepared13.rightRows000`, `PairLightAdaptivePrepared13.rightCached001`, `PairLightAdaptivePrepared13.rightRows001`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData13.lean, lines 8-8, SHA-256 43661d57c14a5835bdef59c169c98f0bdcddb56cd04de34c2b7751231c768249; D1Bound5/SmallPairLightAdaptiveData13.lean, lines 9-9, SHA-256 43661d57c14a5835bdef59c169c98f0bdcddb56cd04de34c2b7751231c768249; D1Bound5/SmallPairLightAdaptiveData13.lean, lines 11-11, SHA-256 43661d57c14a5835bdef59c169c98f0bdcddb56cd04de34c2b7751231c768249; D1Bound5/SmallPairLightAdaptiveData13.lean, lines 12-12, SHA-256 43661d57c14a5835bdef59c169c98f0bdcddb56cd04de34c2b7751231c768249; D1Bound5/SmallPairLightAdaptiveData13.lean, lines 14-14, SHA-256 43661d57c14a5835bdef59c169c98f0bdcddb56cd04de34c2b7751231c768249; D1Bound5/SmallPairLightAdaptiveData13.lean, lines 15-15, SHA-256 43661d57c14a5835bdef59c169c98f0bdcddb56cd04de34c2b7751231c768249; D1Bound5/SmallPairLightAdaptiveData13.lean, lines 17-17, SHA-256 43661d57c14a5835bdef59c169c98f0bdcddb56cd04de34c2b7751231c768249; D1Bound5/SmallPairLightAdaptiveData13.lean, lines 18-18, SHA-256 43661d57c14a5835bdef59c169c98f0bdcddb56cd04de34c2b7751231c768249. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared13.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared13.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 248
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 248

def rightCached000 : List PairLightCachedVertex := PairLightPrepared13.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared13.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 248
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 248


end D1Bound5.PairLightAdaptivePrepared13
end


