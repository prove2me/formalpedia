-- Prove2me | Definitions.Def_D1Bound5_SmallPairClassificationData_Definitions
-- name    : D1Bound5_SmallPairClassificationData_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:16:26.835147+00:00
-- url     : https://prove2.me/theorems/0108cdb8-8662-43c7-8b7a-8954d76b76c2
-- title:
--   Small Pair Classification Data
-- statement:
--   Definitions for small pair classification data in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `smallPairs_0_1`, `smallPairs_0_2`, `smallPairs_0_3`, `smallPairs_0_4`, `smallPairs_0_5`, `smallPairs_0_6`, `smallPairs_0_7`, `smallPairs_0_8` and 20 further declarations.
-- source:
--   D1Bound5/SmallPairClassificationData.lean, lines 9-46, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 48-62, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 64-73, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 75-88, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 90-93, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 95-98, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 100-105, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 107-109, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 111-154, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 156-183, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 185-192, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 194-199, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 201-206, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 208-215, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 217-219, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 221-224, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 226-243, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 245-246, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 252-253, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 259-260, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 266-267, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 273-274, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 280-281, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 287-288, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 294-295, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 301-302, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 308-309, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410; D1Bound5/SmallPairClassificationData.lean, lines 315-316, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def smallPairs_0_1 : List (Finset (ℤ × ℤ)) := [
  {(-2,-2), (-2,2)},
  {(-2,-2), (0,-2)},
  {(-2,-2), (2,0)},
  {(-2,-1), (0,-1)},
  {(-2,-1), (0,2)},
  {(-2,-1), (2,-1)},
  {(-2,0), (-1,-2)},
  {(-2,0), (-1,2)},
  {(-2,0), (1,0)},
  {(-2,0), (2,-2)},
  {(-2,0), (2,2)},
  {(-2,1), (0,-2)},
  {(-2,1), (0,1)},
  {(-2,1), (2,1)},
  {(-2,2), (0,2)},
  {(-2,2), (2,0)},
  {(-1,-2), (1,-2)},
  {(-1,-2), (1,0)},
  {(-1,-1), (1,-1)},
  {(-1,0), (1,-2)},
  {(-1,0), (1,2)},
  {(-1,0), (2,0)},
  {(-1,1), (1,1)},
  {(-1,2), (1,0)},
  {(-1,2), (1,2)},
  {(0,-2), (0,-1)},
  {(0,-2), (2,-2)},
  {(0,-2), (2,1)},
  {(0,-1), (2,-1)},
  {(0,1), (0,2)},
  {(0,1), (2,1)},
  {(0,2), (2,-1)},
  {(0,2), (2,2)},
  {(1,-2), (2,0)},
  {(1,2), (2,0)},
  {(2,-2), (2,2)}
]

def smallPairs_0_2 : List (Finset (ℤ × ℤ)) := [
  {(-2,-1), (0,-1)},
  {(-2,0), (1,-1)},
  {(-2,0), (1,1)},
  {(-2,1), (0,1)},
  {(-1,-1), (-1,1)},
  {(-1,-1), (1,-1)},
  {(-1,-1), (2,0)},
  {(-1,1), (1,1)},
  {(-1,1), (2,0)},
  {(0,-2), (0,2)},
  {(0,-1), (2,-1)},
  {(0,1), (2,1)},
  {(1,-1), (1,1)}
]

def smallPairs_0_3 : List (Finset (ℤ × ℤ)) := [
  {(-2,-1), (0,-1)},
  {(-2,0), (2,0)},
  {(-2,1), (0,1)},
  {(-1,-1), (1,-1)},
  {(-1,1), (1,1)},
  {(0,-1), (0,1)},
  {(0,-1), (2,-1)},
  {(0,1), (2,1)}
]

def smallPairs_0_4 : List (Finset (ℤ × ℤ)) := [
  {(-2,-1), (-2,1)},
  {(-2,-1), (0,-1)},
  {(-2,-1), (2,0)},
  {(-2,0), (2,-1)},
  {(-2,0), (2,1)},
  {(-2,1), (0,1)},
  {(-2,1), (2,0)},
  {(-1,-1), (1,-1)},
  {(-1,1), (1,1)},
  {(0,-1), (2,-1)},
  {(0,1), (2,1)},
  {(2,-1), (2,1)}
]

def smallPairs_0_5 : List (Finset (ℤ × ℤ)) := [
  {(-1,-1), (1,-1)},
  {(-1,1), (1,1)}
]

def smallPairs_0_6 : List (Finset (ℤ × ℤ)) := [
  {(-1,-1), (1,-1)},
  {(-1,1), (1,1)}
]

def smallPairs_0_7 : List (Finset (ℤ × ℤ)) := [
  {(-1,-1), (-1,1)},
  {(-1,-1), (1,-1)},
  {(-1,1), (1,1)},
  {(1,-1), (1,1)}
]

def smallPairs_0_8 : List (Finset (ℤ × ℤ)) := [
  {(0,-1), (0,1)}
]

def smallPairs_1_1 : List (Finset (ℤ × ℤ)) := [
  {(-3,1), (-1,1)},
  {(-3,1), (2,-1)},
  {(-3,2), (-1,2)},
  {(-3,2), (1,-1)},
  {(-2,-1), (0,-1)},
  {(-2,-1), (1,1)},
  {(-2,0), (2,0)},
  {(-2,1), (-1,-1)},
  {(-2,1), (-1,3)},
  {(-2,1), (0,1)},
  {(-2,1), (1,0)},
  {(-2,1), (3,-1)},
  {(-2,2), (0,2)},
  {(-2,3), (-1,0)},
  {(-2,3), (1,1)},
  {(-1,-2), (0,1)},
  {(-1,-2), (1,-2)},
  {(-1,-1), (1,-1)},
  {(-1,-1), (1,0)},
  {(-1,-1), (2,-3)},
  {(-1,-1), (2,1)},
  {(-1,0), (1,-3)},
  {(-1,0), (1,1)},
  {(-1,0), (2,-1)},
  {(-1,1), (-1,2)},
  {(-1,1), (1,1)},
  {(-1,1), (3,-2)},
  {(-1,2), (0,1)},
  {(-1,2), (1,-2)},
  {(-1,2), (1,2)},
  {(-1,3), (1,0)},
  {(0,-2), (2,-2)},
  {(0,-1), (1,-2)},
  {(0,-1), (1,2)},
  {(0,-1), (2,-1)},
  {(0,1), (2,1)},
  {(1,-3), (2,-1)},
  {(1,-2), (1,-1)},
  {(1,-2), (3,-2)},
  {(1,-1), (3,-1)},
  {(1,0), (2,-3)},
  {(1,1), (2,-1)}
]

def smallPairs_1_2 : List (Finset (ℤ × ℤ)) := [
  {(-3,1), (-2,-1)},
  {(-3,1), (-1,1)},
  {(-3,1), (1,-2)},
  {(-3,1), (1,0)},
  {(-3,1), (2,1)},
  {(-2,-1), (-1,2)},
  {(-2,-1), (0,-1)},
  {(-2,-1), (1,0)},
  {(-2,-1), (3,-1)},
  {(-2,1), (0,1)},
  {(-2,1), (2,-1)},
  {(-2,2), (0,-2)},
  {(-2,2), (0,2)},
  {(-1,-1), (1,-1)},
  {(-1,-1), (1,1)},
  {(-1,0), (2,1)},
  {(-1,0), (3,-1)},
  {(-1,1), (1,1)},
  {(-1,2), (3,-1)},
  {(0,-2), (2,-2)},
  {(0,-1), (2,-1)},
  {(0,1), (2,1)},
  {(0,2), (2,-2)},
  {(1,-2), (2,1)},
  {(1,-1), (3,-1)},
  {(2,1), (3,-1)}
]

def smallPairs_1_3 : List (Finset (ℤ × ℤ)) := [
  {(-2,1), (0,1)},
  {(-1,-1), (1,-1)},
  {(-1,1), (0,-1)},
  {(-1,1), (1,1)},
  {(0,-1), (2,-1)},
  {(0,1), (1,-1)}
]

def smallPairs_1_4 : List (Finset (ℤ × ℤ)) := [
  {(-2,1), (0,1)},
  {(-1,-1), (1,-1)},
  {(-1,1), (1,1)},
  {(0,-1), (2,-1)}
]

def smallPairs_1_5 : List (Finset (ℤ × ℤ)) := [
  {(-2,1), (0,1)},
  {(-1,-1), (1,-1)},
  {(-1,1), (1,1)},
  {(0,-1), (2,-1)}
]

def smallPairs_1_6 : List (Finset (ℤ × ℤ)) := [
  {(-2,1), (-1,-1)},
  {(-2,1), (0,1)},
  {(-1,-1), (1,-1)},
  {(-1,1), (1,1)},
  {(0,-1), (2,-1)},
  {(1,1), (2,-1)}
]

def smallPairs_1_7 : List (Finset (ℤ × ℤ)) := [

]

def smallPairs_1_8 : List (Finset (ℤ × ℤ)) := [
  {(-1,1), (0,-1)},
  {(0,1), (1,-1)}
]

def smallPairTable (tau nu : ℤ) : List (Finset (ℤ × ℤ)) :=
  if tau = 0 ∧ nu = 1 then smallPairs_0_1 else
  if tau = 0 ∧ nu = 2 then smallPairs_0_2 else
  if tau = 0 ∧ nu = 3 then smallPairs_0_3 else
  if tau = 0 ∧ nu = 4 then smallPairs_0_4 else
  if tau = 0 ∧ nu = 5 then smallPairs_0_5 else
  if tau = 0 ∧ nu = 6 then smallPairs_0_6 else
  if tau = 0 ∧ nu = 7 then smallPairs_0_7 else
  if tau = 0 ∧ nu = 8 then smallPairs_0_8 else
  if tau = 1 ∧ nu = 1 then smallPairs_1_1 else
  if tau = 1 ∧ nu = 2 then smallPairs_1_2 else
  if tau = 1 ∧ nu = 3 then smallPairs_1_3 else
  if tau = 1 ∧ nu = 4 then smallPairs_1_4 else
  if tau = 1 ∧ nu = 5 then smallPairs_1_5 else
  if tau = 1 ∧ nu = 6 then smallPairs_1_6 else
  if tau = 1 ∧ nu = 7 then smallPairs_1_7 else
  if tau = 1 ∧ nu = 8 then smallPairs_1_8 else
  []

def smallPairRepresentatives_0_1 : Finset (Finset (ℤ × ℤ)) :=
  {{(-2,-2), (-2,2)}, {(-2,-2), (0,-2)}, {(-2,-2), (2,0)}, {(-2,-1), (0,-1)}, {(-2,-1), (0,2)}, {(-2,-1), (2,-1)}, {(-2,0), (-1,-2)}, {(-2,0), (1,0)}, {(-1,-2), (1,-2)}, {(-1,-2), (1,0)}, {(-1,-1), (1,-1)}, {(0,-2), (0,-1)}}



def smallPairRepresentatives_0_2 : Finset (Finset (ℤ × ℤ)) :=
  {{(-2,-1), (0,-1)}, {(-2,0), (1,-1)}, {(-1,-1), (-1,1)}, {(-1,-1), (1,-1)}, {(0,-2), (0,2)}}



def smallPairRepresentatives_1_1 : Finset (Finset (ℤ × ℤ)) :=
  {{(-2,-1), (0,-1)}, {(-2,-1), (1,1)}, {(-1,-2), (1,-2)}, {(-1,-2), (0,1)}, {(-2,0), (2,0)}, {(-1,-1), (-2,1)}, {(-1,-1), (2,-3)}, {(-1,-1), (1,-1)}, {(-1,-1), (1,0)}, {(0,-2), (2,-2)}, {(-1,0), (1,-3)}, {(0,-1), (1,-2)}, {(1,-2), (-1,2)}}



def smallPairRepresentatives_0_5 : Finset (Finset (ℤ × ℤ)) :=
  {{(-1,-1), (1,-1)}}



def smallPairRepresentatives_0_6 : Finset (Finset (ℤ × ℤ)) :=
  {{(-1,-1), (1,-1)}}



def smallPairRepresentatives_1_2 : Finset (Finset (ℤ × ℤ)) :=
  {{(-2,-1), (-3,1)}, {(-2,-1), (0,-1)}, {(-2,-1), (-1,2)}, {(-2,-1), (1,0)}, {(-2,-1), (3,-1)}, {(-1,-1), (1,-1)}, {(-1,-1), (1,1)}, {(0,-2), (-2,2)}, {(0,-2), (2,-2)}}



def smallPairRepresentatives_1_3 : Finset (Finset (ℤ × ℤ)) :=
  {{(-1,-1), (1,-1)}, {(0,-1), (-1,1)}}



def smallPairRepresentatives_1_4 : Finset (Finset (ℤ × ℤ)) :=
  {{(-1,-1), (1,-1)}}



def smallPairRepresentatives_1_5 : Finset (Finset (ℤ × ℤ)) :=
  {{(-1,-1), (1,-1)}}



def smallPairRepresentatives_1_6 : Finset (Finset (ℤ × ℤ)) :=
  {{(-1,-1), (-2,1)}, {(-1,-1), (1,-1)}}



def smallPairRepresentatives_1_8 : Finset (Finset (ℤ × ℤ)) :=
  {{(0,-1), (-1,1)}}





































































end D1Bound5
end


