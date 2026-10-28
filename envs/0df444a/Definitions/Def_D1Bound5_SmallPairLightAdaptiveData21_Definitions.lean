-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData21_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData21_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T03:21:52.272984+00:00
-- url     : https://prove2.me/theorems/8be6e97d-fb12-46ef-ba0f-112eb8bf89fb
-- title:
--   Small Pair Light Adaptive Data21
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared21.leftCached000`, `PairLightAdaptivePrepared21.leftRows000`, `PairLightAdaptivePrepared21.leftCached001`, `PairLightAdaptivePrepared21.leftRows001`, `PairLightAdaptivePrepared21.leftCached002`, `PairLightAdaptivePrepared21.leftRows002`, `PairLightAdaptivePrepared21.leftCached003`, `PairLightAdaptivePrepared21.leftRows003` and 12 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData21.lean, lines 8-9, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 10-10, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 12-13, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 14-14, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 16-17, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 18-18, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 20-21, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 22-22, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 24-25, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 26-26, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 28-29, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 30-30, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 32-33, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 34-34, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 36-37, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 38-38, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 40-41, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 42-42, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 44-45, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094; D1Bound5/SmallPairLightAdaptiveData21.lean, lines 46-46, SHA-256 2b3f4f6170db2d42e8faeac9802331f4d148d7000bcca55a81627914f4133094. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached000 : List PairLightCachedVertex := PairLightPrepared21.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared21.leftRows

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
def rightCached000 : List PairLightCachedVertex := PairLightPrepared21.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared21.rightRows

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


end D1Bound5.PairLightAdaptivePrepared21
end


