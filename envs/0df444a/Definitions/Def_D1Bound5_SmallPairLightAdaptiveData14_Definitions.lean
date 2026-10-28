-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData14_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:44:13.616688+00:00
-- url     : https://prove2.me/theorems/d48ed3dd-870a-4e01-8c70-d302b642052b
-- title:
--   Small Pair Light Adaptive Data14
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared14.leftCached000`, `PairLightAdaptivePrepared14.leftRows000`, `PairLightAdaptivePrepared14.leftCached001`, `PairLightAdaptivePrepared14.leftRows001`, `PairLightAdaptivePrepared14.leftCached002`, `PairLightAdaptivePrepared14.leftRows002`, `PairLightAdaptivePrepared14.leftCached003`, `PairLightAdaptivePrepared14.leftRows003` and 12 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData14.lean, lines 8-9, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 10-10, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 12-13, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 14-14, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 16-17, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 18-18, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 20-21, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 22-22, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 24-25, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 26-26, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 28-29, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 30-30, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 32-33, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 34-34, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 36-37, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 38-38, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 40-41, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 42-42, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 44-45, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851; D1Bound5/SmallPairLightAdaptiveData14.lean, lines 46-46, SHA-256 61a43f97c0887302d3333a939b3fe9ea06819e36d61934a783702c1df521e851. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached000 : List PairLightCachedVertex := PairLightPrepared14.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared14.leftRows

noncomputable
def leftCached001 : List PairLightCachedVertex := leftCached000.drop 88
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 88

noncomputable
def leftCached002 : List PairLightCachedVertex := leftCached001.drop 114
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 114

noncomputable
def leftCached003 : List PairLightCachedVertex := leftCached002.drop 217
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 217

noncomputable
def leftCached004 : List PairLightCachedVertex := leftCached003.drop 76
def leftRows004 : List (Nat × List Nat) := leftRows003.drop 76

noncomputable
def rightCached000 : List PairLightCachedVertex := PairLightPrepared14.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared14.rightRows

noncomputable
def rightCached001 : List PairLightCachedVertex := rightCached000.drop 88
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 88

noncomputable
def rightCached002 : List PairLightCachedVertex := rightCached001.drop 114
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 114

noncomputable
def rightCached003 : List PairLightCachedVertex := rightCached002.drop 215
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 215

noncomputable
def rightCached004 : List PairLightCachedVertex := rightCached003.drop 79
def rightRows004 : List (Nat × List Nat) := rightRows003.drop 79


end D1Bound5.PairLightAdaptivePrepared14
end


