-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData23_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData23_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:41:29.426912+00:00
-- url     : https://prove2.me/theorems/270359fa-1be4-430d-8029-53c209f1c9a4
-- title:
--   Small Pair Light Adaptive Data23
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared23.leftCached000`, `PairLightAdaptivePrepared23.leftRows000`, `PairLightAdaptivePrepared23.leftCached001`, `PairLightAdaptivePrepared23.leftRows001`, `PairLightAdaptivePrepared23.leftCached002`, `PairLightAdaptivePrepared23.leftRows002`, `PairLightAdaptivePrepared23.leftCached003`, `PairLightAdaptivePrepared23.leftRows003` and 8 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData23.lean, lines 8-9, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 10-10, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 12-13, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 14-14, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 16-17, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 18-18, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 20-21, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 22-22, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 24-25, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 26-26, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 28-29, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 30-30, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 32-33, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 34-34, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 36-37, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e; D1Bound5/SmallPairLightAdaptiveData23.lean, lines 38-38, SHA-256 0dea66a45b9602bba47db514cd31af546fe99074fbf8950c227d95d18b0b869e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached000 : List PairLightCachedVertex := PairLightPrepared23.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared23.leftRows

noncomputable
def leftCached001 : List PairLightCachedVertex := leftCached000.drop 91
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 91

noncomputable
def leftCached002 : List PairLightCachedVertex := leftCached001.drop 121
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 121

noncomputable
def leftCached003 : List PairLightCachedVertex := leftCached002.drop 270
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 270

noncomputable
def rightCached000 : List PairLightCachedVertex := PairLightPrepared23.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared23.rightRows

noncomputable
def rightCached001 : List PairLightCachedVertex := rightCached000.drop 92
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 92

noncomputable
def rightCached002 : List PairLightCachedVertex := rightCached001.drop 122
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 122

noncomputable
def rightCached003 : List PairLightCachedVertex := rightCached002.drop 266
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 266


end D1Bound5.PairLightAdaptivePrepared23
end


