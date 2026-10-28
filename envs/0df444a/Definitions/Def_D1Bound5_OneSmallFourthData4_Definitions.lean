-- Prove2me | Definitions.Def_D1Bound5_OneSmallFourthData4_Definitions
-- name    : D1Bound5_OneSmallFourthData4_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:55:50.068306+00:00
-- url     : https://prove2.me/theorems/90c1b51d-15d8-4b4d-88e5-37ac3c35b215
-- title:
--   One Small Fourth Data4
-- statement:
--   Definitions for one small fourth data4 in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `oneSmallTripleS_24`, `oneSmallTripleCutoff_24`, `oneSmallTripleS_25`, `oneSmallTripleCutoff_25`, `oneSmallTripleS_26`, `oneSmallTripleCutoff_26`, `oneSmallTripleS_27`, `oneSmallTripleCutoff_27` and 8 further declarations.
-- source:
--   D1Bound5/OneSmallFourthData4.lean, lines 8-8, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 9-9, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 28-28, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 29-29, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 48-48, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 49-49, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 68-68, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 69-69, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 88-88, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 89-89, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 108-108, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 109-109, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 128-128, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 129-129, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 148-148, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4; D1Bound5/OneSmallFourthData4.lean, lines 149-149, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def oneSmallTripleS_24 : QuadInt 1 1 := ⟨6,9⟩
def oneSmallTripleCutoff_24 : ℤ := 7943





def oneSmallTripleS_25 : QuadInt 1 1 := ⟨11,1⟩
def oneSmallTripleCutoff_25 : ℤ := 6361





def oneSmallTripleS_26 : QuadInt 1 1 := ⟨-6,-3⟩
def oneSmallTripleCutoff_26 : ℤ := 14404





def oneSmallTripleS_27 : QuadInt 1 1 := ⟨-10,9⟩
def oneSmallTripleCutoff_27 : ℤ := 14608





def oneSmallTripleS_28 : QuadInt 1 1 := ⟨-4,8⟩
def oneSmallTripleCutoff_28 : ℤ := 2461





def oneSmallTripleS_29 : QuadInt 1 1 := ⟨-5,4⟩
def oneSmallTripleCutoff_29 : ℤ := 1622





def oneSmallTripleS_30 : QuadInt 1 1 := ⟨-1,-4⟩
def oneSmallTripleCutoff_30 : ℤ := 1622





def oneSmallTripleS_31 : QuadInt 1 1 := ⟨4,-8⟩
def oneSmallTripleCutoff_31 : ℤ := 21270





end D1Bound5
end


