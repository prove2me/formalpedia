-- Prove2me | Definitions.Def_D1Bound5_SmallTripleData_Definitions
-- name    : D1Bound5_SmallTripleData_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:06:00.387396+00:00
-- url     : https://prove2.me/theorems/36bcdfd4-4804-4b21-8dc7-7a9398572d28
-- title:
--   Small Triple Data
-- statement:
--   Simultaneous negation and the coordinate conjugation x+yω ↦ x+τy−yω. The named objects in this bundle include `smallTriples_0_1`, `smallTriples_0_2`, `smallTriples_0_4`, `smallTriples_1_1`, `smallTriples_1_2`, `smallTripleOrbit`, `smallTripleRepresentatives_0_1`, `smallTripleRepresentatives_0_2` and 3 further declarations.
-- source:
--   D1Bound5/SmallTripleData.lean, lines 9-20, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da; D1Bound5/SmallTripleData.lean, lines 22-25, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da; D1Bound5/SmallTripleData.lean, lines 27-30, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da; D1Bound5/SmallTripleData.lean, lines 32-41, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da; D1Bound5/SmallTripleData.lean, lines 43-48, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da; D1Bound5/SmallTripleData.lean, lines 50-55, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da; D1Bound5/SmallTripleData.lean, lines 57-60, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da; D1Bound5/SmallTripleData.lean, lines 61-62, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da; D1Bound5/SmallTripleData.lean, lines 63-65, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da; D1Bound5/SmallTripleData.lean, lines 66-67, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da; D1Bound5/SmallTripleData.lean, lines 78-86, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallTriples_0_1 : List (Finset (ℤ × ℤ)) := [
  {(-2,-2), (-2,2), (2,0)},
  {(-2,-1), (0,-1), (2,-1)},
  {(-2,-1), (0,2), (2,-1)},
  {(-2,0), (-1,-2), (1,0)},
  {(-2,0), (-1,2), (1,0)},
  {(-2,0), (2,-2), (2,2)},
  {(-2,1), (0,-2), (2,1)},
  {(-2,1), (0,1), (2,1)},
  {(-1,0), (1,-2), (2,0)},
  {(-1,0), (1,2), (2,0)}
]

def smallTriples_0_2 : List (Finset (ℤ × ℤ)) := [
  {(-2,0), (1,-1), (1,1)},
  {(-1,-1), (-1,1), (2,0)}
]

def smallTriples_0_4 : List (Finset (ℤ × ℤ)) := [
  {(-2,-1), (-2,1), (2,0)},
  {(-2,0), (2,-1), (2,1)}
]

def smallTriples_1_1 : List (Finset (ℤ × ℤ)) := [
  {(-2,1), (-1,-1), (1,0)},
  {(-2,1), (-1,3), (1,0)},
  {(-2,3), (-1,0), (1,1)},
  {(-1,-1), (1,0), (2,-3)},
  {(-1,0), (1,-3), (2,-1)},
  {(-1,0), (1,1), (2,-1)},
  {(-1,1), (-1,2), (0,1)},
  {(0,-1), (1,-2), (1,-1)}
]

def smallTriples_1_2 : List (Finset (ℤ × ℤ)) := [
  {(-3,1), (-2,-1), (1,0)},
  {(-3,1), (1,-2), (2,1)},
  {(-2,-1), (-1,2), (3,-1)},
  {(-1,0), (2,1), (3,-1)}
]

/-- Simultaneous negation and the coordinate conjugation x+yω ↦ x+τy−yω. -/
def smallTripleOrbit (tau : ℤ) (row : Finset (ℤ × ℤ)) :
    Finset (Finset (ℤ × ℤ)) :=
  {row, row.image (fun p => (-p.1, -p.2)),
    row.image (fun p => (p.1+tau*p.2, -p.2)),
    row.image (fun p => (-p.1-tau*p.2, p.2))}

/-- The ten rows displayed in manuscript Table 7.2, in normalized coordinates. -/
def smallTripleRepresentatives_0_1 : Finset (Finset (ℤ × ℤ)) :=
  {{(-2,-2), (-2,2), (2,0)}, {(-2,-1), (0,-1), (2,-1)},
   {(-2,-1), (0,2), (2,-1)}, {(-2,0), (-1,-2), (1,0)}}
def smallTripleRepresentatives_0_2 : Finset (Finset (ℤ × ℤ)) :=
  {{(-2,0), (1,-1), (1,1)}}
def smallTripleRepresentatives_1_1 : Finset (Finset (ℤ × ℤ)) :=
  {{(-1,-1), (-2,1), (1,0)}, {(-1,-1), (2,-3), (1,0)},
   {(0,-1), (1,-2), (1,-1)}}
def smallTripleRepresentatives_1_2 : Finset (Finset (ℤ × ℤ)) :=
  {{(-2,-1), (-3,1), (1,0)}, {(-2,-1), (-1,2), (3,-1)}}



def smallTripleTable (tau nu : ℤ) : List (Finset (ℤ × ℤ)) :=
  if tau = 0 then
    if nu = 1 then smallTriples_0_1 else
    if nu = 2 then smallTriples_0_2 else
    if nu = 4 then smallTriples_0_4 else []
  else if tau = 1 then
    if nu = 1 then smallTriples_1_1 else
    if nu = 2 then smallTriples_1_2 else []
  else []







































































end D1Bound5
end


