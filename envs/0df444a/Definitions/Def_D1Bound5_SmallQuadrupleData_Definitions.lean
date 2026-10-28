-- Prove2me | Definitions.Def_D1Bound5_SmallQuadrupleData_Definitions
-- name    : D1Bound5_SmallQuadrupleData_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:50:58.099458+00:00
-- url     : https://prove2.me/theorems/b83297ff-a680-45de-8680-91b685708506
-- title:
--   Small Quadruple Data
-- statement:
--   Definitions for small quadruple data in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `smallDisk_0_1`, `smallDisk_0_2`, `smallDisk_0_3`, `smallDisk_0_4`, `smallDisk_0_5`, `smallDisk_0_6`, `smallDisk_0_7`, `smallDisk_0_8` and 8 further declarations.
-- source:
--   D1Bound5/SmallQuadrupleData.lean, lines 9-9, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 24-24, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 39-39, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 54-54, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 69-69, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 84-84, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 99-99, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 114-114, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 129-129, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 144-144, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 159-159, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 174-174, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 189-189, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 204-204, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 219-219, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908; D1Bound5/SmallQuadrupleData.lean, lines 234-234, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def smallDisk_0_1 : List (QuadInt 0 1) := [⟨-2,-2⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-2,2⟩, ⟨-1,-2⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨-1,2⟩, ⟨0,-2⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨1,-2⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨2,-2⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨2,2⟩]







def smallDisk_0_2 : List (QuadInt 0 2) := [⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-2⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩]







def smallDisk_0_3 : List (QuadInt 0 3) := [⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩]







def smallDisk_0_4 : List (QuadInt 0 4) := [⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩]







def smallDisk_0_5 : List (QuadInt 0 5) := [⟨-2,0⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,0⟩]







def smallDisk_0_6 : List (QuadInt 0 6) := [⟨-2,0⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,0⟩]







def smallDisk_0_7 : List (QuadInt 0 7) := [⟨-2,0⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,0⟩]







def smallDisk_0_8 : List (QuadInt 0 8) := [⟨-2,0⟩, ⟨-1,0⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,0⟩, ⟨2,0⟩]







def smallDisk_1_1 : List (QuadInt 1 1) := [⟨-3,1⟩, ⟨-3,2⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-2,2⟩, ⟨-2,3⟩, ⟨-1,-2⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨-1,2⟩, ⟨-1,3⟩, ⟨0,-2⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨1,-3⟩, ⟨1,-2⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨2,-3⟩, ⟨2,-2⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-2⟩, ⟨3,-1⟩]







def smallDisk_1_2 : List (QuadInt 1 2) := [⟨-3,1⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-2,2⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨-1,2⟩, ⟨0,-2⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨1,-2⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-2⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-1⟩]







def smallDisk_1_3 : List (QuadInt 1 3) := [⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩]







def smallDisk_1_4 : List (QuadInt 1 4) := [⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩]







def smallDisk_1_5 : List (QuadInt 1 5) := [⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩]







def smallDisk_1_6 : List (QuadInt 1 6) := [⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩]







def smallDisk_1_7 : List (QuadInt 1 7) := [⟨-2,0⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨2,0⟩]







def smallDisk_1_8 : List (QuadInt 1 8) := [⟨-2,0⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨2,0⟩]









end D1Bound5
end


