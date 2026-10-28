-- Prove2me | Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
-- name    : D1Bound5_OneSmallCutoffArithmetic_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:06:16.698718+00:00
-- url     : https://prove2.me/theorems/8900e9f0-d1de-4160-b24c-a8439b2704e4
-- title:
--   One Small Cutoff Arithmetic 001
-- statement:
--   Exact rational data for a printed fixed-triple cutoff. Coefficient and residual entries are arithmetic parameters here; this record does not assert analytic bounds for any approximating polynomial family. The named objects in this bundle include `OneSmallCutoffRow`, `OneSmallCutoffRow.M2`, `OneSmallCutoffRow.M3`, `OneSmallCutoffRow.M4`, `OneSmallCutoffRow.M5`, `OneSmallCutoffRow.Mbs`, `OneSmallCutoffRow.Mn`, `OneSmallCutoffRow.phi1` and 68 further declarations.
-- source:
--   D1Bound5/OneSmallCutoffArithmetic.lean, lines 6-20, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 24-24, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 25-25, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 26-26, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 27-27, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 28-28, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 29-29, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 31-32, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 34-34, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 35-35, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 36-36, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 37-37, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 38-38, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 39-39, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 41-44, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 46-68, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 70-71, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 73-87, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 89-92, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 99-100, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 105-106, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 111-112, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 117-118, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 123-124, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 129-130, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 135-136, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 141-142, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 147-148, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 153-154, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 159-160, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 165-166, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 171-172, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 177-178, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 183-184, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 189-190, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 195-196, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 201-202, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 207-208, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 213-214, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 219-220, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 225-226, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 231-232, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 237-238, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 243-244, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 249-250, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 255-256, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 261-262, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 267-268, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 273-274, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 279-280, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 285-286, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 291-292, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 297-298, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 303-304, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 309-310, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 315-316, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 321-322, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 327-328, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 333-334, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 339-340, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 345-346, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 351-352, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 357-358, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4; D1Bound5/OneSmallCutoffArithmetic.lean, lines 363-364, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt

/-- Exact rational data for a printed fixed-triple cutoff. Coefficient
and residual entries are arithmetic parameters here; this record does not
assert analytic bounds for any approximating polynomial family. -/
structure OneSmallCutoffRow where
  triple : OneSmallTripleRow
  q1 : ℚ
  phi1 : ℚ
  q : ℚ
  M2 : ℚ
  Mn : ℚ
  M3 : ℚ
  M4 : ℚ
  M5 : ℚ
  Mbs : ℚ
  deriving DecidableEq

namespace OneSmallCutoffRow

def a0 (r : OneSmallCutoffRow) : ℚ := r.triple.anchorA.norm
def b0 (r : OneSmallCutoffRow) : ℚ := r.triple.anchorB.norm
def s0 (r : OneSmallCutoffRow) : ℚ := r.triple.anchorS.norm
def dab (r : OneSmallCutoffRow) : ℚ := (r.triple.anchorA-r.triple.anchorB).norm
def das (r : OneSmallCutoffRow) : ℚ := (r.triple.anchorA-r.triple.anchorS).norm
def dbs (r : OneSmallCutoffRow) : ℚ := (r.triple.anchorB-r.triple.anchorS).norm

def retainedCoefficient (r : OneSmallCutoffRow) : ℚ :=
  (9999/100)*r.a0*(1/r.q1-(51051/400000)/r.b0)^2

def R2 (r : OneSmallCutoffRow) : ℚ := (5/4)*(101/200)*(r.dab/(4*r.b0))^2
def Rn (r : OneSmallCutoffRow) : ℚ := (35/32)*(101/200)*(r.dab/(4*r.b0))^3
def R3 (r : OneSmallCutoffRow) : ℚ := (35/16)*(101/200)*(r.dab/(4*r.b0))^3
def R4 (r : OneSmallCutoffRow) : ℚ := (63/8)*(101/200)*(r.dab/(4*r.b0))^4
def R5 (r : OneSmallCutoffRow) : ℚ := (495/64)*(101/200)*(r.dab/(4*r.b0))^5
def Rbs (r : OneSmallCutoffRow) : ℚ := (3535/409600)*r.phi1

def Rp (r : OneSmallCutoffRow) : ℚ :=
  let x := 1/r.q
  (15+80*x+150*x^2+280*x^3+35*x^4)/256 +
    21*(885+1144*x+435*x^2+2634*x^3+170*x^4)/(1024*999)

/-- The thirteen exact coefficients and powers in the manuscript's
fixed-triple adjacent-overlap table. The two maxima entering P are
represented by separate inequalities. -/
def overlaps (r : OneSmallCutoffRow) : List (ℚ × ℕ) :=
  let K := r.retainedCoefficient
  let b := r.b0
  let s := r.s0
  let h : ℚ := 4001/3999
  let Mm : ℚ := (8/9)*608^2
  let Rm : ℚ := 3920/81
  [((1-1/4000)*K^4/(12100*s^5),5),
   (K^2/(36*r.M2^2*b^4*s^2*h),4),
   (K^2/(16*r.R2^2*2400^2*b^3*s^5*h),5),
   (K^2/(16*r.R2^2*2400^2*b^5*s^4*h),5),
   (K^2/(16*r.Rp^2*r.M3^2*b^6*s^4*h),5),
   (K^4/(16*r.R3^2*Mm^2*b^6*s^12*h),10),
   (K^4/(16*Rm^2*r.Mn^2*b^9*s^9*h),10),
   (K^4/(16*r.Rn^2*r.Mbs^2*b^3*s^11*h),10),
   (K^2/(16*r.Rbs^2*r.M4^2*b^5*s^5*h),5),
   (K^4/(144*r.R4^2*42^8*b^15*s^4*h),10),
   ((2/5)^8*K^4/(4*r.M5^2*b^16*s^4*h),10),
   (K^6/(144*r.R5^2*42^10*b^19*s^6*h),15),
   ((2/5)^10*K^6/(36*42^12*b^22*s^6*h),15)]

def ordinaryTail (r : OneSmallCutoffRow) : ℚ :=
  r.retainedCoefficient^2*(r.triple.cutoff : ℚ)^5/(105^2*r.b0^4*r.s0^2)

/-- All square-root enclosures are verified by rational square
comparisons, followed by all thirteen strict overlap comparisons and
the ordinary-tail comparison at the printed cutoff. -/
def Valid (r : OneSmallCutoffRow) : Prop :=
  1024 ≤ r.triple.cutoff ∧
  (r.a0=1 ∨ (r.a0=2 ∧ 4*r.a0*r.b0*r.s0 < (r.triple.cutoff : ℚ))) ∧
  9 ≤ r.b0 ∧ r.b0 ≤ r.s0 ∧
  2 < r.q ∧ r.q^2 ≤ r.b0/r.a0 ∧
  0 < r.q1 ∧ r.dab*r.das*r.dbs/(r.b0*r.s0^2) ≤ r.q1^2 ∧
  0 ≤ r.phi1 ∧ r.dbs^6/r.s0^6 ≤ r.phi1^2 ∧
  r.b0*r.dbs^5/r.s0^6 ≤ r.phi1^2 ∧
  (51051/400000)/r.b0 < 1/r.q1 ∧ 1 < r.retainedCoefficient ∧
  0 < r.M2 ∧ 0 < r.Mn ∧ 0 < r.M3 ∧ 0 < r.M4 ∧ 0 < r.M5 ∧ 0 < r.Mbs ∧
  (∀ e ∈ r.overlaps, 1 < e.1*(r.triple.cutoff : ℚ)^e.2) ∧
  1 < r.ordinaryTail

instance (r : OneSmallCutoffRow) : Decidable r.Valid :=
by
  unfold Valid
  infer_instance

end OneSmallCutoffRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def oneSmallCutoffRow_0 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (0, 1), (0, -3), (-4, -2), 1024⟩, 13743685419/10000000000, 4913/8000, 3, 62, 608, 280, 12222, 136530, 285⟩



def oneSmallCutoffRow_1 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (0, 1), (0, -3), (4, -2), 1024⟩, 13743685419/10000000000, 4913/8000, 3, 62, 608, 280, 12222, 136530, 285⟩



def oneSmallCutoffRow_2 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (0, 1), (0, -3), (0, 5), 1934⟩, 17066666667/10000000000, 262144/15625, 3, 62, 608, 280, 12222, 136530, 1368⟩



def oneSmallCutoffRow_3 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (0, 1), (0, 5), (0, 10), 2311⟩, 9/25, 1/64, 5, 17, 77, 44, 808, 4011, 42⟩



def oneSmallCutoffRow_4 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (0, 1), (4, -2), (-4, 4), 4770⟩, 698771243/400000000, 15625/512, 44721359549/10000000000, 37, 281, 147, 4610, 38256, 2238⟩



def oneSmallCutoffRow_5 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (0, 1), (4, -2), (8, 1), 2359⟩, 3440104581/5000000000, 56895767/1000000000, 44721359549/10000000000, 37, 281, 147, 4610, 38256, 72⟩



def oneSmallCutoffRow_6 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (0, 1), (4, 4), (6, 9), 3896⟩, 813650973/2000000000, 15996037/1000000000, 28284271247/5000000000, 21, 110, 64, 1402, 8160, 44⟩



def oneSmallCutoffRow_7 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (1, 0), (-5, 0), (-4, -4), 3299⟩, 9900284087/10000000000, 454550753/2500000000, 5, 44, 379, 180, 6340, 61370, 396⟩



def oneSmallCutoffRow_8 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (1, 0), (-5, 0), (-4, 4), 3299⟩, 9900284087/10000000000, 454550753/2500000000, 5, 44, 379, 180, 6340, 61370, 396⟩



def oneSmallCutoffRow_9 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (1, 0), (-4, 4), (-1, 8), 4857⟩, 7180059501/10000000000, 643702123/10000000000, 28284271247/5000000000, 37, 293, 150, 4791, 40361, 172⟩



def oneSmallCutoffRow_10 : OneSmallCutoffRow :=
  ⟨⟨0, 1, (1, 0), (2, 4), (7, 6), 2018⟩, 61953493/125000000, 198567067/5000000000, 44721359549/10000000000, 23, 129, 77, 1798, 11204, 29⟩



def oneSmallCutoffRow_11 : OneSmallCutoffRow :=
  ⟨⟨0, 2, (1, 0), (-3, 0), (-2, -2), 1024⟩, 13743685419/10000000000, 27/64, 3, 62, 608, 280, 12222, 136530, 474⟩



def oneSmallCutoffRow_12 : OneSmallCutoffRow :=
  ⟨⟨0, 2, (1, 0), (-3, 0), (-2, 2), 1024⟩, 13743685419/10000000000, 27/64, 3, 62, 608, 280, 12222, 136530, 474⟩



def oneSmallCutoffRow_13 : OneSmallCutoffRow :=
  ⟨⟨0, 2, (1, 0), (-2, 2), (1, 4), 1024⟩, 1051548627/1250000000, 1367114673/10000000000, 34641016151/10000000000, 45, 377, 183, 6284, 60438, 133⟩



def oneSmallCutoffRow_14 : OneSmallCutoffRow :=
  ⟨⟨0, 2, (1, 0), (1, 4), (6, 6), 4775⟩, 206346493/400000000, 285279493/10000000000, 11489125293/2000000000, 25, 158, 95, 2471, 16976, 56⟩



def oneSmallCutoffRow_15 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (0, 1), (-9, 6), (-13, 13), 13059⟩, 221885351/500000000, 68467501/5000000000, 79372539331/10000000000, 24, 156, 94, 2424, 16601, 77⟩



def oneSmallCutoffRow_16 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (0, 1), (-6, 9), (-8, 16), 12244⟩, 384154411/1000000000, 26629813/2500000000, 79372539331/10000000000, 21, 119, 70, 1599, 9691, 60⟩



def oneSmallCutoffRow_17 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (0, 1), (-5, 1), (-9, 6), 2301⟩, 3099305427/5000000000, 370370371/10000000000, 45825756949/10000000000, 34, 252, 136, 4117, 32986, 74⟩



def oneSmallCutoffRow_18 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (0, 1), (-4, -4), (-10, 1), 9744⟩, 431085853/625000000, 491927019/10000000000, 34641016151/5000000000, 37, 286, 147, 4661, 38983, 180⟩



def oneSmallCutoffRow_19 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (0, 1), (-4, 4), (-6, 9), 1195⟩, 281079793/625000000, 274308431/10000000000, 4, 22, 121, 72, 1618, 9751, 35⟩



def oneSmallCutoffRow_20 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (0, 1), (-1, 5), (-1, 10), 1760⟩, 369361879/1000000000, 20734609/1000000000, 45825756949/10000000000, 17, 73, 41, 741, 3580, 37⟩



def oneSmallCutoffRow_21 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (0, 1), (2, -7), (-4, -4), 7354⟩, 1952562419/2000000000, 2139035547/10000000000, 62449979983/10000000000, 39, 318, 159, 5209, 45613, 430⟩



def oneSmallCutoffRow_22 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (0, 1), (2, -7), (8, -8), 7441⟩, 429142647/500000000, 127466663/1000000000, 62449979983/10000000000, 39, 318, 159, 5209, 45613, 271⟩



def oneSmallCutoffRow_23 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (0, 1), (3, -3), (7, -2), 1024⟩, 8590062503/10000000000, 780609923/5000000000, 3, 48, 401, 193, 6835, 66703, 78⟩



def oneSmallCutoffRow_24 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (0, 1), (4, 4), (6, 9), 7943⟩, 243796413/625000000, 13161149/1000000000, 34641016151/5000000000, 20, 106, 62, 1336, 7678, 48⟩



def oneSmallCutoffRow_25 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (0, 1), (7, -2), (11, 1), 6361⟩, 4900162301/10000000000, 221045507/10000000000, 62449979983/10000000000, 24, 152, 91, 2326, 15710, 48⟩



def oneSmallCutoffRow_26 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (1, 0), (-9, 3), (-6, -3), 14404⟩, 1641829841/2000000000, 120242511/1000000000, 79372539331/10000000000, 36, 276, 143, 4502, 37275, 473⟩



def oneSmallCutoffRow_27 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (1, 0), (-9, 3), (-10, 9), 14608⟩, 6953466039/10000000000, 1408933/25000000, 79372539331/10000000000, 36, 276, 143, 4502, 37275, 272⟩



def oneSmallCutoffRow_28 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (1, 0), (-5, 4), (-4, 8), 2461⟩, 3858387329/5000000000, 104675293/1250000000, 45825756949/10000000000, 40, 323, 162, 5308, 46658, 155⟩



def oneSmallCutoffRow_29 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (1, 0), (-4, 0), (-5, 4), 1622⟩, 2271283813/2000000000, 2631846089/10000000000, 4, 51, 456, 205, 8194, 83910, 422⟩



def oneSmallCutoffRow_30 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (1, 0), (-4, 0), (-1, -4), 1622⟩, 2271283813/2000000000, 2631846089/10000000000, 4, 51, 456, 205, 8194, 83910, 422⟩



def oneSmallCutoffRow_31 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (1, 0), (-4, 8), (4, -8), 21270⟩, 20416666667/10000000000, 64, 34641016151/5000000000, 26, 173, 103, 2780, 19826, 4138⟩



def oneSmallCutoffRow_32 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (1, 0), (-4, 8), (-1, 12), 8968⟩, 205824693/400000000, 61306993/2500000000, 34641016151/5000000000, 26, 173, 103, 2780, 19826, 78⟩



def oneSmallCutoffRow_33 : OneSmallCutoffRow :=
  ⟨⟨1, 1, (1, 0), (2, 5), (7, 7), 5928⟩, 426840257/1000000000, 186741919/10000000000, 62449979983/10000000000, 21, 113, 66, 1460, 8607, 41⟩



def oneSmallCutoffRow_34 : OneSmallCutoffRow :=
  ⟨⟨0, 5, (1, 0), (-6, 0), (-5, -2), 5913⟩, 2222685137/2500000000, 665322101/5000000000, 6, 41, 333, 164, 5461, 49340, 381⟩



def oneSmallCutoffRow_35 : OneSmallCutoffRow :=
  ⟨⟨0, 5, (1, 0), (-6, 0), (-5, 2), 5913⟩, 2222685137/2500000000, 665322101/5000000000, 6, 41, 333, 164, 5461, 49340, 381⟩



def oneSmallCutoffRow_36 : OneSmallCutoffRow :=
  ⟨⟨0, 5, (1, 0), (-5, 2), (-2, 4), 8435⟩, 674687203/1000000000, 10251641/200000000, 16770509831/2500000000, 35, 273, 142, 4450, 36676, 186⟩



def oneSmallCutoffRow_37 : OneSmallCutoffRow :=
  ⟨⟨0, 6, (1, 0), (-7, 0), (-6, -2), 9706⟩, 325485857/400000000, 506365741/5000000000, 7, 38, 303, 153, 4954, 42245, 370⟩



def oneSmallCutoffRow_38 : OneSmallCutoffRow :=
  ⟨⟨0, 6, (1, 0), (-7, 0), (-6, 2), 9706⟩, 325485857/400000000, 506365741/5000000000, 7, 38, 303, 153, 4954, 42245, 370⟩



def oneSmallCutoffRow_39 : OneSmallCutoffRow :=
  ⟨⟨0, 6, (1, 0), (-6, 2), (-3, 4), 13453⟩, 1277298737/2000000000, 209296797/5000000000, 19364916731/2500000000, 34, 259, 137, 4205, 34076, 197⟩



def oneSmallCutoffRow_40 : OneSmallCutoffRow :=
  ⟨⟨1, 2, (1, 0), (-2, 3), (1, 5), 1517⟩, 802873581/1250000000, 692818423/10000000000, 4, 32, 224, 127, 3666, 28238, 67⟩



def oneSmallCutoffRow_41 : OneSmallCutoffRow :=
  ⟨⟨1, 2, (1, 0), (1, 5), (6, 7), 11143⟩, 1106320859/2500000000, 16642829/1000000000, 14966629547/2000000000, 23, 137, 81, 1973, 12709, 57⟩



def oneSmallCutoffRow_42 : OneSmallCutoffRow :=
  ⟨⟨1, 3, (1, 0), (-4, 1), (-3, -1), 1451⟩, 820667637/625000000, 921050751/2000000000, 19364916731/5000000000, 50, 440, 201, 7791, 78839, 646⟩



def oneSmallCutoffRow_43 : OneSmallCutoffRow :=
  ⟨⟨1, 3, (1, 0), (-4, 1), (-3, 3), 1460⟩, 1977930359/2000000000, 1714677641/10000000000, 19364916731/5000000000, 50, 440, 201, 7791, 78839, 261⟩



def oneSmallCutoffRow_44 : OneSmallCutoffRow :=
  ⟨⟨1, 3, (1, 0), (-3, 3), (0, 5), 3590⟩, 6255308857/10000000000, 729/15625, 51961524227/10000000000, 32, 230, 127, 3748, 29208, 94⟩



























































end D1Bound5
end


