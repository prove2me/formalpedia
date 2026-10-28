-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData5_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData5_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:42:18.127437+00:00
-- url     : https://prove2.me/theorems/5edb23d9-2fa4-4360-a788-77e9f29e1e9a
-- title:
--   Small Pair Light Adaptive Data5
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared5.leftCached000`, `PairLightAdaptivePrepared5.leftRows000`, `PairLightAdaptivePrepared5.leftCached001`, `PairLightAdaptivePrepared5.leftRows001`, `PairLightAdaptivePrepared5.leftCached002`, `PairLightAdaptivePrepared5.leftRows002`, `PairLightAdaptivePrepared5.leftCached003`, `PairLightAdaptivePrepared5.leftRows003` and 8 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData5.lean, lines 8-8, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 9-9, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 11-11, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 12-12, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 14-14, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 15-15, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 17-17, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 18-18, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 20-20, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 21-21, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 23-23, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 24-24, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 26-26, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 27-27, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 29-29, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213; D1Bound5/SmallPairLightAdaptiveData5.lean, lines 30-30, SHA-256 ee459846541ba3437ab2cc5fc6b8d5e6890ca8cc69673996315981406742f213. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared5.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared5.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 105
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 105

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 164
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 164

def leftCached003 : List PairLightCachedVertex := leftCached002.drop 162
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 162

def rightCached000 : List PairLightCachedVertex := PairLightPrepared5.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared5.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 106
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 106

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 166
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 166

def rightCached003 : List PairLightCachedVertex := rightCached002.drop 158
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 158


end D1Bound5.PairLightAdaptivePrepared5
end


