-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData15_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData15_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:37:48.838109+00:00
-- url     : https://prove2.me/theorems/8aa54bec-46d9-401b-b9b5-80ade59f3cd8
-- title:
--   Small Pair Light Adaptive Data15
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared15.leftCached000`, `PairLightAdaptivePrepared15.leftRows000`, `PairLightAdaptivePrepared15.leftCached001`, `PairLightAdaptivePrepared15.leftRows001`, `PairLightAdaptivePrepared15.leftCached002`, `PairLightAdaptivePrepared15.leftRows002`, `PairLightAdaptivePrepared15.leftCached003`, `PairLightAdaptivePrepared15.leftRows003` and 8 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData15.lean, lines 8-9, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 10-10, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 12-13, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 14-14, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 16-17, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 18-18, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 20-21, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 22-22, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 24-25, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 26-26, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 28-29, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 30-30, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 32-33, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 34-34, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 36-37, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9; D1Bound5/SmallPairLightAdaptiveData15.lean, lines 38-38, SHA-256 da2c3852387f70aa39c453875f23355adf5beb7667facb54747aa1e6f29566a9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached000 : List PairLightCachedVertex := PairLightPrepared15.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared15.leftRows

noncomputable
def leftCached001 : List PairLightCachedVertex := leftCached000.drop 92
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 92

noncomputable
def leftCached002 : List PairLightCachedVertex := leftCached001.drop 122
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 122

noncomputable
def leftCached003 : List PairLightCachedVertex := leftCached002.drop 267
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 267

noncomputable
def rightCached000 : List PairLightCachedVertex := PairLightPrepared15.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared15.rightRows

noncomputable
def rightCached001 : List PairLightCachedVertex := rightCached000.drop 92
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 92

noncomputable
def rightCached002 : List PairLightCachedVertex := rightCached001.drop 122
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 122

noncomputable
def rightCached003 : List PairLightCachedVertex := rightCached002.drop 266
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 266


end D1Bound5.PairLightAdaptivePrepared15
end


