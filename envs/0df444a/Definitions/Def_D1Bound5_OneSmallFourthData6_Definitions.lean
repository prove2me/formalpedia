-- Prove2me | Definitions.Def_D1Bound5_OneSmallFourthData6_Definitions
-- name    : D1Bound5_OneSmallFourthData6_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:53:54.378931+00:00
-- url     : https://prove2.me/theorems/c2158b86-d68b-42f5-a475-8f408c964330
-- title:
--   One Small Fourth Data6
-- statement:
--   Definitions for one small fourth data6 in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `oneSmallTripleS_40`, `oneSmallTripleCutoff_40`, `oneSmallTripleS_41`, `oneSmallTripleCutoff_41`, `oneSmallTripleS_42`, `oneSmallTripleCutoff_42`, `oneSmallTripleS_43`, `oneSmallTripleCutoff_43` and 8 further declarations.
-- source:
--   D1Bound5/OneSmallFourthData6.lean, lines 8-8, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 9-9, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 28-28, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 29-29, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 48-48, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 49-49, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 68-68, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 69-69, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 88-88, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 89-89, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 108-108, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 109-109, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 128-128, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 129-129, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 148-148, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6; D1Bound5/OneSmallFourthData6.lean, lines 149-149, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def oneSmallTripleS_40 : QuadInt 1 2 := ⟨1,5⟩
def oneSmallTripleCutoff_40 : ℤ := 1517





def oneSmallTripleS_41 : QuadInt 1 2 := ⟨6,7⟩
def oneSmallTripleCutoff_41 : ℤ := 11143





def oneSmallTripleS_42 : QuadInt 1 3 := ⟨-3,-1⟩
def oneSmallTripleCutoff_42 : ℤ := 1451





def oneSmallTripleS_43 : QuadInt 1 3 := ⟨-3,3⟩
def oneSmallTripleCutoff_43 : ℤ := 1460





def oneSmallTripleS_44 : QuadInt 1 3 := ⟨0,5⟩
def oneSmallTripleCutoff_44 : ℤ := 3590





def oneSmallTripleS_45 : QuadInt 1 4 := ⟨-4,-1⟩
def oneSmallTripleCutoff_45 : ℤ := 3059





def oneSmallTripleS_46 : QuadInt 1 4 := ⟨-4,3⟩
def oneSmallTripleCutoff_46 : ℤ := 3090





def oneSmallTripleS_47 : QuadInt 1 4 := ⟨-1,5⟩
def oneSmallTripleCutoff_47 : ℤ := 6843





end D1Bound5
end


