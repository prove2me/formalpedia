-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData18_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:38:49.363085+00:00
-- url     : https://prove2.me/theorems/13916818-2ede-4aa6-ad35-76d9afa8120e
-- title:
--   Small Pair Light Adaptive Data18
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared18.leftCached000`, `PairLightAdaptivePrepared18.leftRows000`, `PairLightAdaptivePrepared18.leftCached001`, `PairLightAdaptivePrepared18.leftRows001`, `PairLightAdaptivePrepared18.rightCached000`, `PairLightAdaptivePrepared18.rightRows000`, `PairLightAdaptivePrepared18.rightCached001`, `PairLightAdaptivePrepared18.rightRows001`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData18.lean, lines 8-8, SHA-256 378276a7a0d9ea7c761042381ff59c7b864d687508ccbbe1ef3765782793025e; D1Bound5/SmallPairLightAdaptiveData18.lean, lines 9-9, SHA-256 378276a7a0d9ea7c761042381ff59c7b864d687508ccbbe1ef3765782793025e; D1Bound5/SmallPairLightAdaptiveData18.lean, lines 11-11, SHA-256 378276a7a0d9ea7c761042381ff59c7b864d687508ccbbe1ef3765782793025e; D1Bound5/SmallPairLightAdaptiveData18.lean, lines 12-12, SHA-256 378276a7a0d9ea7c761042381ff59c7b864d687508ccbbe1ef3765782793025e; D1Bound5/SmallPairLightAdaptiveData18.lean, lines 14-14, SHA-256 378276a7a0d9ea7c761042381ff59c7b864d687508ccbbe1ef3765782793025e; D1Bound5/SmallPairLightAdaptiveData18.lean, lines 15-15, SHA-256 378276a7a0d9ea7c761042381ff59c7b864d687508ccbbe1ef3765782793025e; D1Bound5/SmallPairLightAdaptiveData18.lean, lines 17-17, SHA-256 378276a7a0d9ea7c761042381ff59c7b864d687508ccbbe1ef3765782793025e; D1Bound5/SmallPairLightAdaptiveData18.lean, lines 18-18, SHA-256 378276a7a0d9ea7c761042381ff59c7b864d687508ccbbe1ef3765782793025e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_005

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared18.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared18.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 262
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 262

def rightCached000 : List PairLightCachedVertex := PairLightPrepared18.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared18.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 262
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 262


end D1Bound5.PairLightAdaptivePrepared18
end


