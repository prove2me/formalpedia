-- Prove2me | Definitions.Def_D1Bound5_OneSmallFourthData7_Definitions
-- name    : D1Bound5_OneSmallFourthData7_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:53:37.313725+00:00
-- url     : https://prove2.me/theorems/f5a16ef4-95ff-4da5-a249-d02484c63030
-- title:
--   One Small Fourth Data7
-- statement:
--   Definitions for one small fourth data7 in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `oneSmallTripleS_48`, `oneSmallTripleCutoff_48`, `oneSmallTripleS_49`, `oneSmallTripleCutoff_49`, `oneSmallTripleS_50`, `oneSmallTripleCutoff_50`, `oneSmallTripleS_51`, `oneSmallTripleCutoff_51` and 8 further declarations.
-- source:
--   D1Bound5/OneSmallFourthData7.lean, lines 8-8, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 9-9, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 28-28, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 29-29, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 48-48, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 49-49, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 68-68, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 69-69, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 88-88, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 89-89, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 108-108, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 109-109, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 128-128, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 129-129, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 148-148, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c; D1Bound5/OneSmallFourthData7.lean, lines 149-149, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def oneSmallTripleS_48 : QuadInt 1 5 := ⟨-5,-1⟩
def oneSmallTripleCutoff_48 : ℤ := 5592





def oneSmallTripleS_49 : QuadInt 1 5 := ⟨-5,3⟩
def oneSmallTripleCutoff_49 : ℤ := 5661





def oneSmallTripleS_50 : QuadInt 1 5 := ⟨-2,5⟩
def oneSmallTripleCutoff_50 : ℤ := 11532





def oneSmallTripleS_51 : QuadInt 1 6 := ⟨-6,-1⟩
def oneSmallTripleCutoff_51 : ℤ := 9289





def oneSmallTripleS_52 : QuadInt 1 6 := ⟨-6,3⟩
def oneSmallTripleCutoff_52 : ℤ := 9415





def oneSmallTripleS_53 : QuadInt 0 1 := ⟨-4,0⟩
def oneSmallTripleCutoff_53 : ℤ := 1281





def oneSmallTripleS_54 : QuadInt 0 1 := ⟨4,-4⟩
def oneSmallTripleCutoff_54 : ℤ := 2561





def oneSmallTripleS_55 : QuadInt 0 1 := ⟨8,4⟩
def oneSmallTripleCutoff_55 : ℤ := 6401





end D1Bound5
end


