-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData28_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:42:15.275993+00:00
-- url     : https://prove2.me/theorems/ac4dd8b5-86a6-4db7-9446-e76460bbfd24
-- title:
--   Small Pair Light Adaptive Data28
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared28.leftCached000`, `PairLightAdaptivePrepared28.leftRows000`, `PairLightAdaptivePrepared28.leftCached001`, `PairLightAdaptivePrepared28.leftRows001`, `PairLightAdaptivePrepared28.leftCached002`, `PairLightAdaptivePrepared28.leftRows002`, `PairLightAdaptivePrepared28.leftCached003`, `PairLightAdaptivePrepared28.leftRows003` and 12 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData28.lean, lines 8-9, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 10-10, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 12-13, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 14-14, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 16-17, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 18-18, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 20-21, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 22-22, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 24-25, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 26-26, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 28-29, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 30-30, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 32-33, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 34-34, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 36-37, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 38-38, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 40-41, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 42-42, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 44-45, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4; D1Bound5/SmallPairLightAdaptiveData28.lean, lines 46-46, SHA-256 03955693477f0249f4990aa2c37d30a00d56c7a5c0d9ef2fe64012873c3cb4a4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached000 : List PairLightCachedVertex := PairLightPrepared28.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared28.leftRows

noncomputable
def leftCached001 : List PairLightCachedVertex := leftCached000.drop 82
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 82

noncomputable
def leftCached002 : List PairLightCachedVertex := leftCached001.drop 102
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 102

noncomputable
def leftCached003 : List PairLightCachedVertex := leftCached002.drop 151
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 151

noncomputable
def leftCached004 : List PairLightCachedVertex := leftCached003.drop 189
def leftRows004 : List (Nat × List Nat) := leftRows003.drop 189

noncomputable
def rightCached000 : List PairLightCachedVertex := PairLightPrepared28.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared28.rightRows

noncomputable
def rightCached001 : List PairLightCachedVertex := rightCached000.drop 82
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 82

noncomputable
def rightCached002 : List PairLightCachedVertex := rightCached001.drop 102
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 102

noncomputable
def rightCached003 : List PairLightCachedVertex := rightCached002.drop 151
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 151

noncomputable
def rightCached004 : List PairLightCachedVertex := rightCached003.drop 189
def rightRows004 : List (Nat × List Nat) := rightRows003.drop 189


end D1Bound5.PairLightAdaptivePrepared28
end


