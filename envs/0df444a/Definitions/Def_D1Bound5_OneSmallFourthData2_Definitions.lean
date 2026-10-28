-- Prove2me | Definitions.Def_D1Bound5_OneSmallFourthData2_Definitions
-- name    : D1Bound5_OneSmallFourthData2_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:54:09.833998+00:00
-- url     : https://prove2.me/theorems/1800085c-2f24-44b7-9574-e149979c0d83
-- title:
--   One Small Fourth Data2
-- statement:
--   Definitions for one small fourth data2 in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `oneSmallTripleS_8`, `oneSmallTripleCutoff_8`, `oneSmallTripleS_9`, `oneSmallTripleCutoff_9`, `oneSmallTripleS_10`, `oneSmallTripleCutoff_10`, `oneSmallTripleS_11`, `oneSmallTripleCutoff_11` and 8 further declarations.
-- source:
--   D1Bound5/OneSmallFourthData2.lean, lines 8-8, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 9-9, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 28-28, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 29-29, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 48-48, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 49-49, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 68-68, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 69-69, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 88-88, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 89-89, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 108-108, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 109-109, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 128-128, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 129-129, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 148-148, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593; D1Bound5/OneSmallFourthData2.lean, lines 149-149, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def oneSmallTripleS_8 : QuadInt 0 1 := ⟨-4,4⟩
def oneSmallTripleCutoff_8 : ℤ := 3299





def oneSmallTripleS_9 : QuadInt 0 1 := ⟨-1,8⟩
def oneSmallTripleCutoff_9 : ℤ := 4857





def oneSmallTripleS_10 : QuadInt 0 1 := ⟨7,6⟩
def oneSmallTripleCutoff_10 : ℤ := 2018





def oneSmallTripleS_11 : QuadInt 0 2 := ⟨-2,-2⟩
def oneSmallTripleCutoff_11 : ℤ := 1024





def oneSmallTripleS_12 : QuadInt 0 2 := ⟨-2,2⟩
def oneSmallTripleCutoff_12 : ℤ := 1024





def oneSmallTripleS_13 : QuadInt 0 2 := ⟨1,4⟩
def oneSmallTripleCutoff_13 : ℤ := 1024





def oneSmallTripleS_14 : QuadInt 0 2 := ⟨6,6⟩
def oneSmallTripleCutoff_14 : ℤ := 4775





def oneSmallTripleS_15 : QuadInt 1 1 := ⟨-13,13⟩
def oneSmallTripleCutoff_15 : ℤ := 13059





end D1Bound5
end


