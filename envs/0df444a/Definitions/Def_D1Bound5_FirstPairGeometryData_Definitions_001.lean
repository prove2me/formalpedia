-- Prove2me | Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
-- name    : D1Bound5_FirstPairGeometryData_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:51:10.050951+00:00
-- url     : https://prove2.me/theorems/d692dbac-7574-41de-bfc0-f98dc284735e
-- title:
--   First Pair Geometry Data 001
-- statement:
--   Exact rational geometry data for S≥15. The M entries here are numerical parameters; actual polynomial height bounds are proved in separate modules. The named objects in this bundle include `FirstPairGeometryRow`, `FirstPairGeometryRow.A1`, `FirstPairGeometryRow.B0`, `FirstPairGeometryRow.B1`, `FirstPairGeometryRow.M2`, `FirstPairGeometryRow.M3`, `FirstPairGeometryRow.M4`, `FirstPairGeometryRow.M5` and 71 further declarations.
-- source:
--   D1Bound5/FirstPairGeometryData.lean, lines 6-22, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 26-26, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 27-27, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 28-28, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 29-29, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 30-30, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 32-32, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 33-33, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 34-34, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 35-35, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 36-37, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 38-39, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 40-40, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 42-42, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 43-43, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 44-44, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 45-45, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 46-46, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 47-50, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 52-74, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 76-76, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 78-87, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 89-91, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 98-99, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 104-105, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 110-111, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 116-117, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 122-123, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 128-129, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 134-135, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 140-141, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 146-147, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 152-153, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 158-159, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 164-165, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 170-171, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 176-177, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 182-183, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 188-189, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 194-195, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 200-201, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 206-207, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 212-213, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 218-219, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 224-225, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 230-231, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 236-237, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 242-243, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 248-249, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 254-255, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 260-261, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 266-267, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 272-273, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 278-279, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 284-285, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 290-291, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 296-297, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 302-303, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 308-309, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 314-315, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 320-321, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 326-327, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 332-333, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 338-339, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a. Project: https://github.com/tomislav-math/d1-bound5-lean

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

/-- Exact rational geometry data for S≥15. The M entries here are numerical
parameters; actual polynomial height bounds are proved in separate modules. -/
structure FirstPairGeometryRow where
  tau : ℤ
  nu : ℤ
  a : ℤ × ℤ
  b : ℤ × ℤ
  A1 : ℚ
  B0 : ℚ
  B1 : ℚ
  d1 : ℚ
  M2 : ℚ
  Mn : ℚ
  M3 : ℚ
  M4 : ℚ
  M5 : ℚ
  deriving DecidableEq

namespace FirstPairGeometryRow

def anchorA (r : FirstPairGeometryRow) : QuadInt r.tau r.nu := ⟨r.a.1,r.a.2⟩
def anchorB (r : FirstPairGeometryRow) : QuadInt r.tau r.nu := ⟨r.b.1,r.b.2⟩
def a0 (r : FirstPairGeometryRow) : ℚ := r.anchorA.norm
def b0 (r : FirstPairGeometryRow) : ℚ := r.anchorB.norm
def dab (r : FirstPairGeometryRow) : ℚ := (r.anchorA-r.anchorB).norm

def q (r : FirstPairGeometryRow) : ℚ := r.B0/r.A1
def Q0 (r : FirstPairGeometryRow) : ℚ := r.d1*(1+r.A1/15)*(1+r.B1/15)
def K (r : FirstPairGeometryRow) : ℚ := (9999/100)*r.a0*(1/r.Q0-(51051/400000)/r.b0)^2
def G (r : FirstPairGeometryRow) : ℚ := r.K*(59/20)^5
def H (r : FirstPairGeometryRow) : ℚ :=
  (9999/100)*r.a0*(59/20)^5*(1-(51051/400000)*r.Q0/r.b0)^2
def F0 (r : FirstPairGeometryRow) : ℚ :=
  (r.dab/r.b0)*(1+r.A1/15)^2*(1+r.B1/15)^8
def rho (r : FirstPairGeometryRow) : ℚ := r.H/((3535/409600)*r.F0)

def R2 (r : FirstPairGeometryRow) : ℚ := (5/4)*(101/200)*(r.dab/(4*r.b0))^2
def Rn (r : FirstPairGeometryRow) : ℚ := (35/32)*(101/200)*(r.dab/(4*r.b0))^3
def R3 (r : FirstPairGeometryRow) : ℚ := (35/16)*(101/200)*(r.dab/(4*r.b0))^3
def R4 (r : FirstPairGeometryRow) : ℚ := (63/8)*(101/200)*(r.dab/(4*r.b0))^4
def R5 (r : FirstPairGeometryRow) : ℚ := (495/64)*(101/200)*(r.dab/(4*r.b0))^5
def Rp (r : FirstPairGeometryRow) : ℚ :=
  let x := 1/r.q
  (15+80*x+150*x^2+280*x^3+35*x^4)/256+
    21*(885+1144*x+435*x^2+2634*x^3+170*x^4)/(1024*999)

/-- All fifteen common-window quotients, with A replaced by one,
B²=b0 and S²=225, including both optional detours. -/
def overlaps (r : FirstPairGeometryRow) : List ℚ :=
  let b := r.b0
  let G := r.G
  let h : ℚ := 4001/3999
  let Mm : ℚ := (8/9)*608^2
  let Rm : ℚ := 3920/81
  [9604*(1-1/4000)*b^5/12100,
   784*225^2/(36*r.M2^2*h),
   G^2*b^2/(16*r.R2^2*2400^2*h),
   G^2*225/(16*r.R2^2*2400^2*h),
   G^2/(16*r.Rp^2*r.Mn^2*h),
   G^2/(16*r.Rp^2*r.M3^2*h),
   G^4/(16*r.R3^2*Mm^2*h),
   G^4*b*225/(16*Rm^2*r.Mn^2*h),
   G^2*b^2/(16*r.Rn^2*r.M4^2*h),
   G^4*b^4/(16*r.Rn^2*4143^2*h),
   r.rho^2/(16*r.M4^2*h),
   G^4*b/(144*r.R4^2*42^8*h),
   G^4/(4*r.M5^2*(5/2)^8*h),
   G^6*b^5/(144*r.R5^2*42^10*h),
   G^6*b^2/(36*42^12*(5/2)^10*h)]

def tail (r : FirstPairGeometryRow) : ℚ := r.G*r.B0*15^3/105

def Valid (r : FirstPairGeometryRow) : Prop :=
  (r.a0=1 ∨ r.a0=2) ∧ 9 ≤ r.b0 ∧ 0 < r.dab ∧
  0 < r.A1 ∧ r.a0 ≤ r.A1^2 ∧
  0 < r.B0 ∧ r.B0^2 ≤ r.b0 ∧ 0 < r.B1 ∧ r.b0 ≤ r.B1^2 ∧
  0 < r.d1 ∧ r.dab/r.b0 ≤ r.d1^2 ∧
  2 < r.q ∧ 0 < r.Q0 ∧ (51051/400000)/r.b0 < 1/r.Q0 ∧
  7/4 < r.K ∧ 0 < r.G ∧ 0 < r.H ∧ 0 < r.F0 ∧ 0 < r.rho ∧
  0 < r.R2 ∧ 0 < r.Rn ∧ 0 < r.R3 ∧ 0 < r.R4 ∧ 0 < r.R5 ∧ 0 < r.Rp ∧
  0 < r.M2 ∧ 0 < r.Mn ∧ 0 < r.M3 ∧ 0 < r.M4 ∧ 0 < r.M5 ∧
  (∀ v ∈ r.overlaps, 59/50 < v) ∧ 1 < r.tail

instance (r : FirstPairGeometryRow) : Decidable r.Valid := by
  unfold Valid
  infer_instance

end FirstPairGeometryRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def firstPairGeometryRow_0 : FirstPairGeometryRow :=
  ⟨0,1,(0,1),(0,-3),1,3,3,66666667/50000000,62,608,280,12222,136530⟩



def firstPairGeometryRow_1 : FirstPairGeometryRow :=
  ⟨0,1,(0,1),(0,5),1,5,5,4/5,17,77,44,808,4011⟩



def firstPairGeometryRow_2 : FirstPairGeometryRow :=
  ⟨0,1,(0,1),(4,-2),1,89442719/20000000,111803399/25000000,111803399/100000000,37,281,147,4610,38256⟩



def firstPairGeometryRow_3 : FirstPairGeometryRow :=
  ⟨0,1,(0,1),(4,4),1,35355339/6250000,22627417/4000000,22097087/25000000,21,110,64,1402,8160⟩



def firstPairGeometryRow_4 : FirstPairGeometryRow :=
  ⟨0,1,(1,0),(-5,0),1,5,5,6/5,44,379,180,6340,61370⟩



def firstPairGeometryRow_5 : FirstPairGeometryRow :=
  ⟨0,1,(1,0),(-4,4),1,35355339/6250000,22627417/4000000,22638463/20000000,37,293,150,4791,40361⟩



def firstPairGeometryRow_6 : FirstPairGeometryRow :=
  ⟨0,1,(1,0),(2,4),1,89442719/20000000,111803399/25000000,18439089/20000000,23,129,77,1798,11204⟩



def firstPairGeometryRow_7 : FirstPairGeometryRow :=
  ⟨0,2,(1,0),(-3,0),1,3,3,66666667/50000000,62,608,280,12222,136530⟩



def firstPairGeometryRow_8 : FirstPairGeometryRow :=
  ⟨0,2,(1,0),(-2,2),1,346410161/100000000,173205081/50000000,1859747/1562500,45,377,183,6284,60438⟩



def firstPairGeometryRow_9 : FirstPairGeometryRow :=
  ⟨0,2,(1,0),(1,4),1,71807033/12500000,114891253/20000000,98473193/100000000,25,158,95,2471,16976⟩



def firstPairGeometryRow_10 : FirstPairGeometryRow :=
  ⟨1,1,(0,1),(-9,6),1,793725393/100000000,396862697/50000000,98399897/100000000,24,156,94,2424,16601⟩



def firstPairGeometryRow_11 : FirstPairGeometryRow :=
  ⟨1,1,(0,1),(-6,9),1,793725393/100000000,396862697/50000000,90851353/100000000,21,119,70,1599,9691⟩



def firstPairGeometryRow_12 : FirstPairGeometryRow :=
  ⟨1,1,(0,1),(-5,1),1,458257569/100000000,45825757/10000000,54554473/50000000,34,252,136,4117,32986⟩



def firstPairGeometryRow_13 : FirstPairGeometryRow :=
  ⟨1,1,(0,1),(-4,-4),1,692820323/100000000,173205081/25000000,28182811/25000000,37,286,147,4661,38983⟩



def firstPairGeometryRow_14 : FirstPairGeometryRow :=
  ⟨1,1,(0,1),(-4,4),1,4,4,45069391/50000000,22,121,72,1618,9751⟩



def firstPairGeometryRow_15 : FirstPairGeometryRow :=
  ⟨1,1,(0,1),(-1,5),1,458257569/100000000,45825757/10000000,3933979/5000000,17,73,41,741,3580⟩



def firstPairGeometryRow_16 : FirstPairGeometryRow :=
  ⟨1,1,(0,1),(2,-7),1,624499799/100000000,3122499/500000,57735027/50000000,39,318,159,5209,45613⟩



def firstPairGeometryRow_17 : FirstPairGeometryRow :=
  ⟨1,1,(0,1),(3,-3),1,3,3,120185043/100000000,48,401,193,6835,66703⟩



def firstPairGeometryRow_18 : FirstPairGeometryRow :=
  ⟨1,1,(0,1),(4,4),1,692820323/100000000,173205081/25000000,17559423/20000000,20,106,62,1336,7678⟩



def firstPairGeometryRow_19 : FirstPairGeometryRow :=
  ⟨1,1,(0,1),(7,-2),1,624499799/100000000,3122499/500000,48701077/50000000,24,152,91,2326,15710⟩



def firstPairGeometryRow_20 : FirstPairGeometryRow :=
  ⟨1,1,(1,0),(-9,3),1,793725393/100000000,396862697/50000000,27995181/25000000,36,276,143,4502,37275⟩



def firstPairGeometryRow_21 : FirstPairGeometryRow :=
  ⟨1,1,(1,0),(-5,4),1,458257569/100000000,45825757/10000000,57735027/50000000,40,323,162,5308,46658⟩



def firstPairGeometryRow_22 : FirstPairGeometryRow :=
  ⟨1,1,(1,0),(-4,0),1,4,4,5/4,51,456,205,8194,83910⟩



def firstPairGeometryRow_23 : FirstPairGeometryRow :=
  ⟨1,1,(1,0),(-4,8),1,692820323/100000000,173205081/25000000,50518149/50000000,26,173,103,2780,19826⟩



def firstPairGeometryRow_24 : FirstPairGeometryRow :=
  ⟨1,1,(1,0),(2,5),1,624499799/100000000,3122499/500000,89155583/100000000,21,113,66,1460,8607⟩



def firstPairGeometryRow_25 : FirstPairGeometryRow :=
  ⟨0,5,(1,0),(-6,0),1,6,6,116666667/100000000,41,333,164,5461,49340⟩



def firstPairGeometryRow_26 : FirstPairGeometryRow :=
  ⟨0,5,(1,0),(-5,2),1,670820393/100000000,335410197/50000000,111554671/100000000,35,273,142,4450,36676⟩



def firstPairGeometryRow_27 : FirstPairGeometryRow :=
  ⟨0,6,(1,0),(-7,0),1,7,7,22857143/20000000,38,303,153,4954,42245⟩



def firstPairGeometryRow_28 : FirstPairGeometryRow :=
  ⟨0,6,(1,0),(-6,2),1,774596669/100000000,77459667/10000000,22060523/20000000,34,259,137,4205,34076⟩



def firstPairGeometryRow_29 : FirstPairGeometryRow :=
  ⟨1,2,(1,0),(-2,3),1,4,4,53033009/50000000,32,224,127,3666,28238⟩



def firstPairGeometryRow_30 : FirstPairGeometryRow :=
  ⟨1,2,(1,0),(1,5),1,748331477/100000000,374165739/50000000,94491119/100000000,23,137,81,1973,12709⟩



def firstPairGeometryRow_31 : FirstPairGeometryRow :=
  ⟨1,3,(1,0),(-4,1),1,193649167/50000000,77459667/20000000,61913919/50000000,50,440,201,7791,78839⟩



def firstPairGeometryRow_32 : FirstPairGeometryRow :=
  ⟨1,3,(1,0),(-3,3),1,259807621/50000000,519615243/100000000,26787919/25000000,32,230,127,3748,29208⟩



def firstPairGeometryRow_33 : FirstPairGeometryRow :=
  ⟨1,4,(1,0),(-5,1),1,122474487/25000000,489897949/100000000,1859747/1562500,44,367,176,6049,57935⟩



def firstPairGeometryRow_34 : FirstPairGeometryRow :=
  ⟨1,4,(1,0),(-4,3),1,158113883/25000000,632455533/100000000,107238053/100000000,32,229,126,3718,28965⟩



def firstPairGeometryRow_35 : FirstPairGeometryRow :=
  ⟨1,5,(1,0),(-6,1),1,295803989/50000000,591607979/100000000,57940857/50000000,40,324,161,5305,46974⟩



def firstPairGeometryRow_36 : FirstPairGeometryRow :=
  ⟨1,5,(1,0),(-5,3),1,92702481/12500000,741619849/100000000,107025911/100000000,31,226,124,3660,28401⟩



def firstPairGeometryRow_37 : FirstPairGeometryRow :=
  ⟨1,6,(1,0),(-7,1),1,692820323/100000000,173205081/25000000,22730303/20000000,37,296,151,4834,40902⟩



def firstPairGeometryRow_38 : FirstPairGeometryRow :=
  ⟨0,1,(1,1),(-1,-3),141421357/100000000,158113883/50000000,316227767/100000000,141421357/100000000,77,803,387,17946,216405⟩



def firstPairGeometryRow_39 : FirstPairGeometryRow :=
  ⟨0,1,(1,1),(3,1),141421357/100000000,158113883/50000000,316227767/100000000,31622777/50000000,19,38,41,370,985⟩



def firstPairGeometryRow_40 : FirstPairGeometryRow :=
  ⟨0,1,(1,0),(3,0),1,3,3,66666667/100000000,12,41,25,300,1100⟩





























end D1Bound5
end


