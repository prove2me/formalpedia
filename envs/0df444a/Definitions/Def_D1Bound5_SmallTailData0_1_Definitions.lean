-- Prove2me | Definitions.Def_D1Bound5_SmallTailData0_1_Definitions
-- name    : D1Bound5_SmallTailData0_1_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:54:40.640232+00:00
-- url     : https://prove2.me/theorems/75af33cf-6cb5-48ec-962a-aa81ad94c568
-- title:
--   Small Tail Data0 1
-- statement:
--   Definitions for small tail data0 1 in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `tailDisk_0_1`.
-- source:
--   D1Bound5/SmallTailData0_1.lean, lines 8-8, SHA-256 e8193c82da9fe118ab3eb160cf6f8da07be08bcc7943ff257aee829c26a5ca2e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def tailDisk_0_1 : List (QuadInt 0 1) := [⟨-3,-2⟩, ⟨-3,-1⟩, ⟨-3,0⟩, ⟨-3,1⟩, ⟨-3,2⟩, ⟨-2,-3⟩, ⟨-2,-2⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-2,2⟩, ⟨-2,3⟩, ⟨-1,-3⟩, ⟨-1,-2⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨-1,2⟩, ⟨-1,3⟩, ⟨0,-3⟩, ⟨0,-2⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨0,3⟩, ⟨1,-3⟩, ⟨1,-2⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨1,3⟩, ⟨2,-3⟩, ⟨2,-2⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨2,2⟩, ⟨2,3⟩, ⟨3,-2⟩, ⟨3,-1⟩, ⟨3,0⟩, ⟨3,1⟩, ⟨3,2⟩]







end D1Bound5
end


