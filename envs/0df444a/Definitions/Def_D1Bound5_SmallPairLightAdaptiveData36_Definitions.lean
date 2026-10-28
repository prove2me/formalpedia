-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData36_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:39:52.137694+00:00
-- url     : https://prove2.me/theorems/257e00fe-3eff-4098-a091-f12d39bbc64e
-- title:
--   Small Pair Light Adaptive Data36
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared36.leftCached000`, `PairLightAdaptivePrepared36.leftRows000`, `PairLightAdaptivePrepared36.leftCached001`, `PairLightAdaptivePrepared36.leftRows001`, `PairLightAdaptivePrepared36.leftCached002`, `PairLightAdaptivePrepared36.leftRows002`, `PairLightAdaptivePrepared36.leftCached003`, `PairLightAdaptivePrepared36.leftRows003` and 12 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData36.lean, lines 8-9, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 10-10, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 12-13, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 14-14, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 16-17, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 18-18, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 20-21, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 22-22, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 24-25, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 26-26, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 28-29, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 30-30, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 32-33, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 34-34, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 36-37, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 38-38, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 40-41, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 42-42, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 44-45, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e; D1Bound5/SmallPairLightAdaptiveData36.lean, lines 46-46, SHA-256 f3712480401c740dc989b7387e90e12554cc61e3cc9688fe8555aa52892f649e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached000 : List PairLightCachedVertex := PairLightPrepared36.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared36.leftRows

noncomputable
def leftCached001 : List PairLightCachedVertex := leftCached000.drop 76
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 76

noncomputable
def leftCached002 : List PairLightCachedVertex := leftCached001.drop 91
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 91

noncomputable
def leftCached003 : List PairLightCachedVertex := leftCached002.drop 119
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 119

noncomputable
def leftCached004 : List PairLightCachedVertex := leftCached003.drop 275
def leftRows004 : List (Nat × List Nat) := leftRows003.drop 275

noncomputable
def rightCached000 : List PairLightCachedVertex := PairLightPrepared36.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared36.rightRows

noncomputable
def rightCached001 : List PairLightCachedVertex := rightCached000.drop 76
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 76

noncomputable
def rightCached002 : List PairLightCachedVertex := rightCached001.drop 91
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 91

noncomputable
def rightCached003 : List PairLightCachedVertex := rightCached002.drop 120
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 120

noncomputable
def rightCached004 : List PairLightCachedVertex := rightCached003.drop 273
def rightRows004 : List (Nat × List Nat) := rightRows003.drop 273


end D1Bound5.PairLightAdaptivePrepared36
end


