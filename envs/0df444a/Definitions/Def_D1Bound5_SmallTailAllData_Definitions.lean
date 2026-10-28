-- Prove2me | Definitions.Def_D1Bound5_SmallTailAllData_Definitions
-- name    : D1Bound5_SmallTailAllData_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:50:35.629992+00:00
-- url     : https://prove2.me/theorems/75a44eee-b40c-4354-b6f3-44cfaef866c2
-- title:
--   Small Tail All Data
-- statement:
--   Definitions for small tail all data in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `tailDisk_0_2`, `tailDisk_0_3`, `tailDisk_0_4`, `tailDisk_0_5`, `tailDisk_0_6`, `tailDisk_0_7`, `tailDisk_0_8`, `tailDisk_0_9` and 20 further declarations.
-- source:
--   D1Bound5/SmallTailAllData.lean, lines 9-9, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 26-26, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 43-43, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 60-60, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 77-77, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 94-94, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 111-111, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 128-128, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 145-145, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 162-162, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 179-179, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 196-196, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 213-213, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 230-230, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 247-247, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 264-264, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 281-281, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 298-298, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 315-315, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 332-332, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 349-349, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 366-366, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 383-383, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 400-400, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 417-417, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 434-434, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 451-451, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1; D1Bound5/SmallTailAllData.lean, lines 468-468, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def tailDisk_0_2 : List (QuadInt 0 2) := [⟨-3,-1⟩, ⟨-3,0⟩, ⟨-3,1⟩, ⟨-2,-2⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-2,2⟩, ⟨-1,-2⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨-1,2⟩, ⟨0,-2⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨1,-2⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨2,-2⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨2,2⟩, ⟨3,-1⟩, ⟨3,0⟩, ⟨3,1⟩]







def tailDisk_0_3 : List (QuadInt 0 3) := [⟨-3,-1⟩, ⟨-3,0⟩, ⟨-3,1⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-2⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨-1,2⟩, ⟨0,-2⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨1,-2⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-1⟩, ⟨3,0⟩, ⟨3,1⟩]







def tailDisk_0_4 : List (QuadInt 0 4) := [⟨-3,-1⟩, ⟨-3,0⟩, ⟨-3,1⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-1⟩, ⟨3,0⟩, ⟨3,1⟩]







def tailDisk_0_5 : List (QuadInt 0 5) := [⟨-3,-1⟩, ⟨-3,0⟩, ⟨-3,1⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-1⟩, ⟨3,0⟩, ⟨3,1⟩]







def tailDisk_0_6 : List (QuadInt 0 6) := [⟨-3,-1⟩, ⟨-3,0⟩, ⟨-3,1⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-1⟩, ⟨3,0⟩, ⟨3,1⟩]







def tailDisk_0_7 : List (QuadInt 0 7) := [⟨-3,0⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,0⟩]







def tailDisk_0_8 : List (QuadInt 0 8) := [⟨-3,0⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,0⟩]







def tailDisk_0_9 : List (QuadInt 0 9) := [⟨-3,0⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,0⟩]







def tailDisk_0_10 : List (QuadInt 0 10) := [⟨-3,0⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,0⟩]







def tailDisk_0_11 : List (QuadInt 0 11) := [⟨-3,0⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,0⟩]







def tailDisk_0_12 : List (QuadInt 0 12) := [⟨-3,0⟩, ⟨-2,0⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,0⟩, ⟨3,0⟩]







def tailDisk_0_13 : List (QuadInt 0 13) := [⟨-3,0⟩, ⟨-2,0⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,0⟩, ⟨3,0⟩]







def tailDisk_0_14 : List (QuadInt 0 14) := [⟨-3,0⟩, ⟨-2,0⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,0⟩, ⟨3,0⟩]







def tailDisk_1_1 : List (QuadInt 1 1) := [⟨-4,1⟩, ⟨-4,2⟩, ⟨-4,3⟩, ⟨-3,-1⟩, ⟨-3,0⟩, ⟨-3,1⟩, ⟨-3,2⟩, ⟨-3,3⟩, ⟨-3,4⟩, ⟨-2,-2⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-2,2⟩, ⟨-2,3⟩, ⟨-2,4⟩, ⟨-1,-3⟩, ⟨-1,-2⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨-1,2⟩, ⟨-1,3⟩, ⟨-1,4⟩, ⟨0,-3⟩, ⟨0,-2⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨0,3⟩, ⟨1,-4⟩, ⟨1,-3⟩, ⟨1,-2⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨1,3⟩, ⟨2,-4⟩, ⟨2,-3⟩, ⟨2,-2⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨2,2⟩, ⟨3,-4⟩, ⟨3,-3⟩, ⟨3,-2⟩, ⟨3,-1⟩, ⟨3,0⟩, ⟨3,1⟩, ⟨4,-3⟩, ⟨4,-2⟩, ⟨4,-1⟩]







def tailDisk_1_2 : List (QuadInt 1 2) := [⟨-4,1⟩, ⟨-3,-1⟩, ⟨-3,0⟩, ⟨-3,1⟩, ⟨-3,2⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-2,2⟩, ⟨-1,-2⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨-1,2⟩, ⟨0,-2⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨1,-2⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨2,-2⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-2⟩, ⟨3,-1⟩, ⟨3,0⟩, ⟨3,1⟩, ⟨4,-1⟩]







def tailDisk_1_3 : List (QuadInt 1 3) := [⟨-4,1⟩, ⟨-3,-1⟩, ⟨-3,0⟩, ⟨-3,1⟩, ⟨-3,2⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-2,2⟩, ⟨-1,-2⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨-1,2⟩, ⟨0,-2⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨1,-2⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨2,-2⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-2⟩, ⟨3,-1⟩, ⟨3,0⟩, ⟨3,1⟩, ⟨4,-1⟩]







def tailDisk_1_4 : List (QuadInt 1 4) := [⟨-3,0⟩, ⟨-3,1⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨-1,2⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-2⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-1⟩, ⟨3,0⟩]







def tailDisk_1_5 : List (QuadInt 1 5) := [⟨-3,0⟩, ⟨-3,1⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-1⟩, ⟨3,0⟩]







def tailDisk_1_6 : List (QuadInt 1 6) := [⟨-3,0⟩, ⟨-3,1⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-1⟩, ⟨3,0⟩]







def tailDisk_1_7 : List (QuadInt 1 7) := [⟨-3,0⟩, ⟨-3,1⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-1⟩, ⟨3,0⟩]







def tailDisk_1_8 : List (QuadInt 1 8) := [⟨-3,0⟩, ⟨-3,1⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-1⟩, ⟨3,0⟩]







def tailDisk_1_9 : List (QuadInt 1 9) := [⟨-3,0⟩, ⟨-3,1⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨3,-1⟩, ⟨3,0⟩]







def tailDisk_1_10 : List (QuadInt 1 10) := [⟨-3,0⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨3,0⟩]







def tailDisk_1_11 : List (QuadInt 1 11) := [⟨-3,0⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨3,0⟩]







def tailDisk_1_12 : List (QuadInt 1 12) := [⟨-3,0⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨3,0⟩]







def tailDisk_1_13 : List (QuadInt 1 13) := [⟨-3,0⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨2,-1⟩, ⟨2,0⟩, ⟨3,0⟩]







def tailDisk_1_14 : List (QuadInt 1 14) := [⟨-3,0⟩, ⟨-2,0⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨2,0⟩, ⟨3,0⟩]







def tailDisk_1_15 : List (QuadInt 1 15) := [⟨-3,0⟩, ⟨-2,0⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨0,-1⟩, ⟨0,0⟩, ⟨0,1⟩, ⟨1,-1⟩, ⟨1,0⟩, ⟨2,0⟩, ⟨3,0⟩]









end D1Bound5
end


