-- Prove2me | Definitions.Def_D1Bound5_OneSmallFourthData1_Definitions
-- name    : D1Bound5_OneSmallFourthData1_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:53:36.950315+00:00
-- url     : https://prove2.me/theorems/7a5fabd2-c09b-4c51-a74b-cda613bdb8ea
-- title:
--   One Small Fourth Data1
-- statement:
--   Definitions for one small fourth data1 in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `oneSmallTripleS_0`, `oneSmallTripleCutoff_0`, `oneSmallTripleS_1`, `oneSmallTripleCutoff_1`, `oneSmallTripleS_2`, `oneSmallTripleCutoff_2`, `oneSmallTripleS_3`, `oneSmallTripleCutoff_3` and 8 further declarations.
-- source:
--   D1Bound5/OneSmallFourthData1.lean, lines 8-8, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 9-9, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 28-28, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 29-29, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 48-48, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 49-49, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 68-68, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 69-69, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 88-88, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 89-89, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 108-108, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 109-109, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 128-128, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 129-129, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 148-148, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125; D1Bound5/OneSmallFourthData1.lean, lines 149-149, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def oneSmallTripleS_0 : QuadInt 0 1 := ⟨-4,-2⟩
def oneSmallTripleCutoff_0 : ℤ := 1024





def oneSmallTripleS_1 : QuadInt 0 1 := ⟨4,-2⟩
def oneSmallTripleCutoff_1 : ℤ := 1024





def oneSmallTripleS_2 : QuadInt 0 1 := ⟨0,5⟩
def oneSmallTripleCutoff_2 : ℤ := 1934





def oneSmallTripleS_3 : QuadInt 0 1 := ⟨0,10⟩
def oneSmallTripleCutoff_3 : ℤ := 2311





def oneSmallTripleS_4 : QuadInt 0 1 := ⟨-4,4⟩
def oneSmallTripleCutoff_4 : ℤ := 4770





def oneSmallTripleS_5 : QuadInt 0 1 := ⟨8,1⟩
def oneSmallTripleCutoff_5 : ℤ := 2359





def oneSmallTripleS_6 : QuadInt 0 1 := ⟨6,9⟩
def oneSmallTripleCutoff_6 : ℤ := 3896





def oneSmallTripleS_7 : QuadInt 0 1 := ⟨-4,-4⟩
def oneSmallTripleCutoff_7 : ℤ := 3299





end D1Bound5
end


