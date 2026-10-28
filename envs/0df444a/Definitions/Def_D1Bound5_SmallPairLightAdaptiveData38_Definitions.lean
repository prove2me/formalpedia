-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData38_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:38:23.733988+00:00
-- url     : https://prove2.me/theorems/d2f8f013-030a-4eb5-95d1-152be2c96e0e
-- title:
--   Small Pair Light Adaptive Data38
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared38.leftCached000`, `PairLightAdaptivePrepared38.leftRows000`, `PairLightAdaptivePrepared38.leftCached001`, `PairLightAdaptivePrepared38.leftRows001`, `PairLightAdaptivePrepared38.rightCached000`, `PairLightAdaptivePrepared38.rightRows000`, `PairLightAdaptivePrepared38.rightCached001`, `PairLightAdaptivePrepared38.rightRows001`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData38.lean, lines 8-8, SHA-256 1617a2228a010f5557d728ebdebefcdb8cc716f0197cf327c9585fc9e217d08d; D1Bound5/SmallPairLightAdaptiveData38.lean, lines 9-9, SHA-256 1617a2228a010f5557d728ebdebefcdb8cc716f0197cf327c9585fc9e217d08d; D1Bound5/SmallPairLightAdaptiveData38.lean, lines 11-11, SHA-256 1617a2228a010f5557d728ebdebefcdb8cc716f0197cf327c9585fc9e217d08d; D1Bound5/SmallPairLightAdaptiveData38.lean, lines 12-12, SHA-256 1617a2228a010f5557d728ebdebefcdb8cc716f0197cf327c9585fc9e217d08d; D1Bound5/SmallPairLightAdaptiveData38.lean, lines 14-14, SHA-256 1617a2228a010f5557d728ebdebefcdb8cc716f0197cf327c9585fc9e217d08d; D1Bound5/SmallPairLightAdaptiveData38.lean, lines 15-15, SHA-256 1617a2228a010f5557d728ebdebefcdb8cc716f0197cf327c9585fc9e217d08d; D1Bound5/SmallPairLightAdaptiveData38.lean, lines 17-17, SHA-256 1617a2228a010f5557d728ebdebefcdb8cc716f0197cf327c9585fc9e217d08d; D1Bound5/SmallPairLightAdaptiveData38.lean, lines 18-18, SHA-256 1617a2228a010f5557d728ebdebefcdb8cc716f0197cf327c9585fc9e217d08d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_005

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared38.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared38.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 280
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 280

def rightCached000 : List PairLightCachedVertex := PairLightPrepared38.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared38.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 281
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 281


end D1Bound5.PairLightAdaptivePrepared38
end


