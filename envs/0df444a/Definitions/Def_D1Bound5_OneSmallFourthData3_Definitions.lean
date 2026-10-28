-- Prove2me | Definitions.Def_D1Bound5_OneSmallFourthData3_Definitions
-- name    : D1Bound5_OneSmallFourthData3_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:57:19.006492+00:00
-- url     : https://prove2.me/theorems/7235865f-8c24-4614-8999-57b652557b15
-- title:
--   One Small Fourth Data3
-- statement:
--   Definitions for one small fourth data3 in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `oneSmallTripleS_16`, `oneSmallTripleCutoff_16`, `oneSmallTripleS_17`, `oneSmallTripleCutoff_17`, `oneSmallTripleS_18`, `oneSmallTripleCutoff_18`, `oneSmallTripleS_19`, `oneSmallTripleCutoff_19` and 8 further declarations.
-- source:
--   D1Bound5/OneSmallFourthData3.lean, lines 8-8, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 9-9, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 28-28, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 29-29, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 48-48, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 49-49, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 68-68, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 69-69, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 88-88, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 89-89, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 108-108, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 109-109, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 128-128, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 129-129, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 148-148, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273; D1Bound5/OneSmallFourthData3.lean, lines 149-149, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def oneSmallTripleS_16 : QuadInt 1 1 := ⟨-8,16⟩
def oneSmallTripleCutoff_16 : ℤ := 12244





def oneSmallTripleS_17 : QuadInt 1 1 := ⟨-9,6⟩
def oneSmallTripleCutoff_17 : ℤ := 2301





def oneSmallTripleS_18 : QuadInt 1 1 := ⟨-10,1⟩
def oneSmallTripleCutoff_18 : ℤ := 9744





def oneSmallTripleS_19 : QuadInt 1 1 := ⟨-6,9⟩
def oneSmallTripleCutoff_19 : ℤ := 1195





def oneSmallTripleS_20 : QuadInt 1 1 := ⟨-1,10⟩
def oneSmallTripleCutoff_20 : ℤ := 1760





def oneSmallTripleS_21 : QuadInt 1 1 := ⟨-4,-4⟩
def oneSmallTripleCutoff_21 : ℤ := 7354





def oneSmallTripleS_22 : QuadInt 1 1 := ⟨8,-8⟩
def oneSmallTripleCutoff_22 : ℤ := 7441





def oneSmallTripleS_23 : QuadInt 1 1 := ⟨7,-2⟩
def oneSmallTripleCutoff_23 : ℤ := 1024





end D1Bound5
end


