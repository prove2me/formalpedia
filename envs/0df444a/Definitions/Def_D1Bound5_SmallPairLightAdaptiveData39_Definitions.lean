-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData39_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData39_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:43:13.875269+00:00
-- url     : https://prove2.me/theorems/2c4aaf5d-ecd8-4e2a-a5dd-a83ef6cff172
-- title:
--   Small Pair Light Adaptive Data39
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared39.leftCached000`, `PairLightAdaptivePrepared39.leftRows000`, `PairLightAdaptivePrepared39.leftCached001`, `PairLightAdaptivePrepared39.leftRows001`, `PairLightAdaptivePrepared39.leftCached002`, `PairLightAdaptivePrepared39.leftRows002`, `PairLightAdaptivePrepared39.leftCached003`, `PairLightAdaptivePrepared39.leftRows003` and 8 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData39.lean, lines 8-9, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 10-10, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 12-13, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 14-14, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 16-17, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 18-18, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 20-21, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 22-22, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 24-25, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 26-26, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 28-29, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 30-30, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 32-33, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 34-34, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 36-37, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332; D1Bound5/SmallPairLightAdaptiveData39.lean, lines 38-38, SHA-256 0292f199da3227edffd561b7ffda7fb7e6160bcfdf76e286e5df9e3c29100332. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached000 : List PairLightCachedVertex := PairLightPrepared39.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared39.leftRows

noncomputable
def leftCached001 : List PairLightCachedVertex := leftCached000.drop 97
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 97

noncomputable
def leftCached002 : List PairLightCachedVertex := leftCached001.drop 136
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 136

noncomputable
def leftCached003 : List PairLightCachedVertex := leftCached002.drop 225
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 225

noncomputable
def rightCached000 : List PairLightCachedVertex := PairLightPrepared39.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared39.rightRows

noncomputable
def rightCached001 : List PairLightCachedVertex := rightCached000.drop 98
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 98

noncomputable
def rightCached002 : List PairLightCachedVertex := rightCached001.drop 138
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 138

noncomputable
def rightCached003 : List PairLightCachedVertex := rightCached002.drop 220
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 220


end D1Bound5.PairLightAdaptivePrepared39
end


