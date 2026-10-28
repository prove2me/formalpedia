-- Prove2me | Definitions.Def_D1Bound5_OneSmallFourthData5_Definitions
-- name    : D1Bound5_OneSmallFourthData5_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:53:49.026423+00:00
-- url     : https://prove2.me/theorems/1ca03122-b7f4-4a0c-b89b-7408662b6e23
-- title:
--   One Small Fourth Data5
-- statement:
--   Definitions for one small fourth data5 in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `oneSmallTripleS_32`, `oneSmallTripleCutoff_32`, `oneSmallTripleS_33`, `oneSmallTripleCutoff_33`, `oneSmallTripleS_34`, `oneSmallTripleCutoff_34`, `oneSmallTripleS_35`, `oneSmallTripleCutoff_35` and 8 further declarations.
-- source:
--   D1Bound5/OneSmallFourthData5.lean, lines 8-8, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 9-9, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 28-28, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 29-29, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 48-48, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 49-49, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 68-68, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 69-69, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 88-88, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 89-89, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 108-108, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 109-109, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 128-128, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 129-129, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 148-148, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83; D1Bound5/OneSmallFourthData5.lean, lines 149-149, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def oneSmallTripleS_32 : QuadInt 1 1 := ⟨-1,12⟩
def oneSmallTripleCutoff_32 : ℤ := 8968





def oneSmallTripleS_33 : QuadInt 1 1 := ⟨7,7⟩
def oneSmallTripleCutoff_33 : ℤ := 5928





def oneSmallTripleS_34 : QuadInt 0 5 := ⟨-5,-2⟩
def oneSmallTripleCutoff_34 : ℤ := 5913





def oneSmallTripleS_35 : QuadInt 0 5 := ⟨-5,2⟩
def oneSmallTripleCutoff_35 : ℤ := 5913





def oneSmallTripleS_36 : QuadInt 0 5 := ⟨-2,4⟩
def oneSmallTripleCutoff_36 : ℤ := 8435





def oneSmallTripleS_37 : QuadInt 0 6 := ⟨-6,-2⟩
def oneSmallTripleCutoff_37 : ℤ := 9706





def oneSmallTripleS_38 : QuadInt 0 6 := ⟨-6,2⟩
def oneSmallTripleCutoff_38 : ℤ := 9706





def oneSmallTripleS_39 : QuadInt 0 6 := ⟨-3,4⟩
def oneSmallTripleCutoff_39 : ℤ := 13453





end D1Bound5
end


