-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData10_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData10_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:41:43.989981+00:00
-- url     : https://prove2.me/theorems/ae6835b0-075c-4c13-89b8-d27e3f76b5cb
-- title:
--   Small Pair Light Adaptive Data10
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared10.leftCached000`, `PairLightAdaptivePrepared10.leftRows000`, `PairLightAdaptivePrepared10.leftCached001`, `PairLightAdaptivePrepared10.leftRows001`, `PairLightAdaptivePrepared10.leftCached002`, `PairLightAdaptivePrepared10.leftRows002`, `PairLightAdaptivePrepared10.leftCached003`, `PairLightAdaptivePrepared10.leftRows003` and 16 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData10.lean, lines 8-8, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 9-9, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 11-11, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 12-12, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 14-14, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 15-15, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 17-17, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 18-18, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 20-20, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 21-21, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 23-23, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 24-24, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 26-26, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 27-27, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 29-29, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 30-30, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 32-32, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 33-33, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 35-35, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 36-36, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 38-38, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 39-39, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 41-41, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682; D1Bound5/SmallPairLightAdaptiveData10.lean, lines 42-42, SHA-256 c9e58a146fe8edabb6741cb59cb54204f99654e0e97b5cc2ddf6a74a29dbd682. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCached000 : List PairLightCachedVertex := PairLightPrepared10.leftCached
noncomputable def leftRows000 : List (Nat × List Nat) := PairLightPrepared10.leftRows

noncomputable def leftCached001 : List PairLightCachedVertex := leftCached000.drop 71
noncomputable def leftRows001 : List (Nat × List Nat) := leftRows000.drop 71

noncomputable def leftCached002 : List PairLightCachedVertex := leftCached001.drop 82
noncomputable def leftRows002 : List (Nat × List Nat) := leftRows001.drop 82

noncomputable def leftCached003 : List PairLightCachedVertex := leftCached002.drop 102
noncomputable def leftRows003 : List (Nat × List Nat) := leftRows002.drop 102

noncomputable def leftCached004 : List PairLightCachedVertex := leftCached003.drop 150
noncomputable def leftRows004 : List (Nat × List Nat) := leftRows003.drop 150

noncomputable def leftCached005 : List PairLightCachedVertex := leftCached004.drop 191
noncomputable def leftRows005 : List (Nat × List Nat) := leftRows004.drop 191

noncomputable def rightCached000 : List PairLightCachedVertex := PairLightPrepared10.rightCached
noncomputable def rightRows000 : List (Nat × List Nat) := PairLightPrepared10.rightRows

noncomputable def rightCached001 : List PairLightCachedVertex := rightCached000.drop 71
noncomputable def rightRows001 : List (Nat × List Nat) := rightRows000.drop 71

noncomputable def rightCached002 : List PairLightCachedVertex := rightCached001.drop 82
noncomputable def rightRows002 : List (Nat × List Nat) := rightRows001.drop 82

noncomputable def rightCached003 : List PairLightCachedVertex := rightCached002.drop 102
noncomputable def rightRows003 : List (Nat × List Nat) := rightRows002.drop 102

noncomputable def rightCached004 : List PairLightCachedVertex := rightCached003.drop 150
noncomputable def rightRows004 : List (Nat × List Nat) := rightRows003.drop 150

noncomputable def rightCached005 : List PairLightCachedVertex := rightCached004.drop 191
noncomputable def rightRows005 : List (Nat × List Nat) := rightRows004.drop 191


end D1Bound5.PairLightAdaptivePrepared10
end


