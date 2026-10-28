-- Prove2me | Definitions.Def_D1Bound5_FirstPairData_Definitions
-- name    : D1Bound5_FirstPairData_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:59:20.339985+00:00
-- url     : https://prove2.me/theorems/b21a0ab7-fcf3-44a1-bd86-875c585983b1
-- title:
--   First Pair Data
-- statement:
--   Definitions for first pair data in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `firstPairOrbit`, `firstPairs_0_1`, `firstPairs_0_2`, `firstPairs_0_3`, `firstPairs_0_4`, `firstPairs_0_5`, `firstPairs_0_6`, `firstPairs_0_7` and 20 further declarations.
-- source:
--   D1Bound5/FirstPairData.lean, lines 8-12, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 14-15, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 17-18, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 20-21, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 23-24, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 26-27, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 29-30, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 32-33, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 35-36, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 38-39, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 41-42, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 44-45, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 47-48, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 50-51, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 53-54, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 56-57, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 59-60, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 62-79, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 81-82, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 88-89, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 95-96, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 102-103, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 109-110, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 116-117, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 123-124, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 130-131, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 137-138, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5; D1Bound5/FirstPairData.lean, lines 144-145, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def firstPairOrbit (tau : ℤ) (row : (ℤ × ℤ) × (ℤ × ℤ)) :
    Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {row, ((-row.1.1,-row.1.2),(-row.2.1,-row.2.2)),
   ((row.1.1+tau*row.1.2,-row.1.2),(row.2.1+tau*row.2.2,-row.2.2)),
   ((-row.1.1-tau*row.1.2,row.1.2),(-row.2.1-tau*row.2.2,row.2.2))}

def firstPairs_0_1 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,-1),(-3,-1)), ((-1,-1),(1,3)), ((-1,0),(-2,-4)), ((-1,0),(-2,4)), ((-1,0),(4,-4)), ((-1,0),(4,4)), ((-1,0),(5,0)), ((-1,1),(-3,1)), ((-1,1),(1,-3)), ((0,-1),(-4,-4)), ((0,-1),(-4,2)), ((0,-1),(0,-5)), ((0,-1),(0,3)), ((0,-1),(4,-4)), ((0,-1),(4,2)), ((0,1),(-4,-2)), ((0,1),(-4,4)), ((0,1),(0,-3)), ((0,1),(0,5)), ((0,1),(4,-2)), ((0,1),(4,4)), ((1,-1),(-1,3)), ((1,-1),(3,-1)), ((1,0),(-5,0)), ((1,0),(-4,-4)), ((1,0),(-4,4)), ((1,0),(2,-4)), ((1,0),(2,4)), ((1,1),(-1,-3)), ((1,1),(3,1))]

def firstPairs_0_2 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(-1,-4)), ((-1,0),(-1,4)), ((-1,0),(2,-2)), ((-1,0),(2,2)), ((-1,0),(3,0)), ((1,0),(-3,0)), ((1,0),(-2,-2)), ((1,0),(-2,2)), ((1,0),(1,-4)), ((1,0),(1,4))]

def firstPairs_0_3 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(0,-4)), ((-1,0),(0,4)), ((-1,0),(3,-2)), ((-1,0),(3,2)), ((-1,0),(4,0)), ((1,0),(-4,0)), ((1,0),(-3,-2)), ((1,0),(-3,2)), ((1,0),(0,-4)), ((1,0),(0,4))]

def firstPairs_0_4 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(4,-2)), ((-1,0),(4,2)), ((-1,0),(5,0)), ((1,0),(-5,0)), ((1,0),(-4,-2)), ((1,0),(-4,2))]

def firstPairs_0_5 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(5,-2)), ((-1,0),(5,2)), ((-1,0),(6,0)), ((1,0),(-6,0)), ((1,0),(-5,-2)), ((1,0),(-5,2))]

def firstPairs_0_6 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(6,-2)), ((-1,0),(6,2)), ((-1,0),(7,0)), ((1,0),(-7,0)), ((1,0),(-6,-2)), ((1,0),(-6,2))]

def firstPairs_0_7 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  []

def firstPairs_0_8 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  []

def firstPairs_1_1 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(-7,5)), ((-1,0),(-4,8)), ((-1,0),(-2,-5)), ((-1,0),(1,4)), ((-1,0),(4,-8)), ((-1,0),(4,0)), ((-1,0),(5,-4)), ((-1,0),(6,3)), ((-1,0),(9,-3)), ((-1,1),(-8,4)), ((-1,1),(-5,-2)), ((-1,1),(-4,5)), ((-1,1),(-3,9)), ((-1,1),(0,-3)), ((-1,1),(0,4)), ((-1,1),(3,6)), ((-1,1),(4,1)), ((-1,1),(5,-7)), ((-1,1),(8,-4)), ((0,-1),(-7,2)), ((0,-1),(-4,-4)), ((0,-1),(-3,3)), ((0,-1),(-2,7)), ((0,-1),(1,-5)), ((0,-1),(4,-4)), ((0,-1),(4,4)), ((0,-1),(5,-1)), ((0,-1),(6,-9)), ((0,-1),(9,-6)), ((0,1),(-9,6)), ((0,1),(-6,9)), ((0,1),(-5,1)), ((0,1),(-4,-4)), ((0,1),(-4,4)), ((0,1),(-1,5)), ((0,1),(2,-7)), ((0,1),(3,-3)), ((0,1),(4,4)), ((0,1),(7,-2)), ((1,-1),(-8,4)), ((1,-1),(-5,7)), ((1,-1),(-4,-1)), ((1,-1),(-3,-6)), ((1,-1),(0,-4)), ((1,-1),(0,3)), ((1,-1),(3,-9)), ((1,-1),(4,-5)), ((1,-1),(5,2)), ((1,-1),(8,-4)), ((1,0),(-9,3)), ((1,0),(-6,-3)), ((1,0),(-5,4)), ((1,0),(-4,0)), ((1,0),(-4,8)), ((1,0),(-1,-4)), ((1,0),(2,5)), ((1,0),(4,-8)), ((1,0),(7,-5))]

def firstPairs_1_2 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(-6,5)), ((-1,0),(-1,-5)), ((-1,0),(-1,3)), ((-1,0),(2,-3)), ((1,0),(-2,3)), ((1,0),(1,-3)), ((1,0),(1,5)), ((1,0),(6,-5))]

def firstPairs_1_3 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(0,3)), ((-1,0),(3,-3)), ((-1,0),(3,1)), ((-1,0),(4,-1)), ((1,0),(-4,1)), ((1,0),(-3,-1)), ((1,0),(-3,3)), ((1,0),(0,-3))]

def firstPairs_1_4 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(1,3)), ((-1,0),(4,-3)), ((-1,0),(4,1)), ((-1,0),(5,-1)), ((1,0),(-5,1)), ((1,0),(-4,-1)), ((1,0),(-4,3)), ((1,0),(-1,-3))]

def firstPairs_1_5 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(2,3)), ((-1,0),(5,-3)), ((-1,0),(5,1)), ((-1,0),(6,-1)), ((1,0),(-6,1)), ((1,0),(-5,-1)), ((1,0),(-5,3)), ((1,0),(-2,-3))]

def firstPairs_1_6 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(6,1)), ((-1,0),(7,-1)), ((1,0),(-7,1)), ((1,0),(-6,-1))]

def firstPairs_1_7 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-1,0),(7,1)), ((-1,0),(8,-1)), ((1,0),(-8,1)), ((1,0),(-7,-1))]

def firstPairs_1_8 : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  []

def firstPairTable (tau nu : ℤ) : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  if tau = 0 ∧ nu = 1 then firstPairs_0_1 else
  if tau = 0 ∧ nu = 2 then firstPairs_0_2 else
  if tau = 0 ∧ nu = 3 then firstPairs_0_3 else
  if tau = 0 ∧ nu = 4 then firstPairs_0_4 else
  if tau = 0 ∧ nu = 5 then firstPairs_0_5 else
  if tau = 0 ∧ nu = 6 then firstPairs_0_6 else
  if tau = 0 ∧ nu = 7 then firstPairs_0_7 else
  if tau = 0 ∧ nu = 8 then firstPairs_0_8 else
  if tau = 1 ∧ nu = 1 then firstPairs_1_1 else
  if tau = 1 ∧ nu = 2 then firstPairs_1_2 else
  if tau = 1 ∧ nu = 3 then firstPairs_1_3 else
  if tau = 1 ∧ nu = 4 then firstPairs_1_4 else
  if tau = 1 ∧ nu = 5 then firstPairs_1_5 else
  if tau = 1 ∧ nu = 6 then firstPairs_1_6 else
  if tau = 1 ∧ nu = 7 then firstPairs_1_7 else
  if tau = 1 ∧ nu = 8 then firstPairs_1_8 else
  []

def firstPairRepresentatives_0_1 : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {((0,1),(0,-3)), ((0,1),(0,5)), ((0,1),(4,-2)), ((0,1),(4,4)), ((1,0),(-5,0)), ((1,0),(-4,4)), ((1,0),(2,4)), ((1,1),(-1,-3)), ((1,1),(3,1))}



def firstPairRepresentatives_0_2 : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {((1,0),(-3,0)), ((1,0),(-2,2)), ((1,0),(1,4))}



def firstPairRepresentatives_0_5 : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {((1,0),(-6,0)), ((1,0),(-5,2))}



def firstPairRepresentatives_0_6 : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {((1,0),(-7,0)), ((1,0),(-6,2))}



def firstPairRepresentatives_1_1 : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {((0,1),(-9,6)), ((0,1),(-6,9)), ((0,1),(-5,1)), ((0,1),(-4,-4)), ((0,1),(-4,4)), ((0,1),(-1,5)), ((0,1),(2,-7)), ((0,1),(3,-3)), ((0,1),(4,4)), ((0,1),(7,-2)), ((1,0),(-9,3)), ((1,0),(-5,4)), ((1,0),(-4,0)), ((1,0),(-4,8)), ((1,0),(2,5))}



def firstPairRepresentatives_1_2 : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {((1,0),(-2,3)), ((1,0),(1,5))}



def firstPairRepresentatives_1_3 : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {((1,0),(-4,1)), ((1,0),(-3,3))}



def firstPairRepresentatives_1_4 : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {((1,0),(-5,1)), ((1,0),(-4,3))}



def firstPairRepresentatives_1_5 : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {((1,0),(-6,1)), ((1,0),(-5,3))}



def firstPairRepresentatives_1_6 : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {((1,0),(-7,1))}





































































end D1Bound5
end


