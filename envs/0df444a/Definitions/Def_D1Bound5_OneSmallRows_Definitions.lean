-- Prove2me | Definitions.Def_D1Bound5_OneSmallRows_Definitions
-- name    : D1Bound5_OneSmallRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:51:47.924986+00:00
-- url     : https://prove2.me/theorems/0193441f-f506-49ae-85e3-1d1d187be339
-- title:
--   One Small Rows
-- statement:
--   The complete fixed-triple certificate record from the manuscript. The named objects in this bundle include `OneSmallTripleRow`, `OneSmallTripleRow.a`, `OneSmallTripleRow.b`, `OneSmallTripleRow.cutoff`, `OneSmallTripleRow.nu`, `OneSmallTripleRow.s`, `OneSmallTripleRow.tau`, `instDecidableEqOneSmallTripleRow` and 9 further declarations.
-- source:
--   D1Bound5/OneSmallRows.lean, lines 12-20, SHA-256 5d9e96e3d46ca1e91403fd677ac916a5fa55d59330a9fc532fee6467ec77e849; D1Bound5/OneSmallRows.lean, lines 22-78, SHA-256 5d9e96e3d46ca1e91403fd677ac916a5fa55d59330a9fc532fee6467ec77e849; D1Bound5/OneSmallRows.lean, lines 80-80, SHA-256 5d9e96e3d46ca1e91403fd677ac916a5fa55d59330a9fc532fee6467ec77e849; D1Bound5/OneSmallRows.lean, lines 81-81, SHA-256 5d9e96e3d46ca1e91403fd677ac916a5fa55d59330a9fc532fee6467ec77e849; D1Bound5/OneSmallRows.lean, lines 82-82, SHA-256 5d9e96e3d46ca1e91403fd677ac916a5fa55d59330a9fc532fee6467ec77e849; D1Bound5/OneSmallRows.lean, lines 149-151, SHA-256 5d9e96e3d46ca1e91403fd677ac916a5fa55d59330a9fc532fee6467ec77e849; D1Bound5/OneSmallRows.lean, lines 153-156, SHA-256 5d9e96e3d46ca1e91403fd677ac916a5fa55d59330a9fc532fee6467ec77e849. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
namespace D1Bound5
open QuadInt

/-- The complete fixed-triple certificate record from the manuscript. -/
structure OneSmallTripleRow where
  tau : ℤ
  nu : ℤ
  a : ℤ × ℤ
  b : ℤ × ℤ
  s : ℤ × ℤ
  cutoff : ℤ
  deriving DecidableEq, Repr

def oneSmallFixedRows : Finset OneSmallTripleRow :=
  {⟨0,1,(0,1),(0,-3),(-4,-2),1024⟩,
   ⟨0,1,(0,1),(0,-3),(4,-2),1024⟩,
   ⟨0,1,(0,1),(0,-3),(0,5),1934⟩,
   ⟨0,1,(0,1),(0,5),(0,10),2311⟩,
   ⟨0,1,(0,1),(4,-2),(-4,4),4770⟩,
   ⟨0,1,(0,1),(4,-2),(8,1),2359⟩,
   ⟨0,1,(0,1),(4,4),(6,9),3896⟩,
   ⟨0,1,(1,0),(-5,0),(-4,-4),3299⟩,
   ⟨0,1,(1,0),(-5,0),(-4,4),3299⟩,
   ⟨0,1,(1,0),(-4,4),(-1,8),4857⟩,
   ⟨0,1,(1,0),(2,4),(7,6),2018⟩,
   ⟨0,2,(1,0),(-3,0),(-2,-2),1024⟩,
   ⟨0,2,(1,0),(-3,0),(-2,2),1024⟩,
   ⟨0,2,(1,0),(-2,2),(1,4),1024⟩,
   ⟨0,2,(1,0),(1,4),(6,6),4775⟩,
   ⟨1,1,(0,1),(-9,6),(-13,13),13059⟩,
   ⟨1,1,(0,1),(-6,9),(-8,16),12244⟩,
   ⟨1,1,(0,1),(-5,1),(-9,6),2301⟩,
   ⟨1,1,(0,1),(-4,-4),(-10,1),9744⟩,
   ⟨1,1,(0,1),(-4,4),(-6,9),1195⟩,
   ⟨1,1,(0,1),(-1,5),(-1,10),1760⟩,
   ⟨1,1,(0,1),(2,-7),(-4,-4),7354⟩,
   ⟨1,1,(0,1),(2,-7),(8,-8),7441⟩,
   ⟨1,1,(0,1),(3,-3),(7,-2),1024⟩,
   ⟨1,1,(0,1),(4,4),(6,9),7943⟩,
   ⟨1,1,(0,1),(7,-2),(11,1),6361⟩,
   ⟨1,1,(1,0),(-9,3),(-6,-3),14404⟩,
   ⟨1,1,(1,0),(-9,3),(-10,9),14608⟩,
   ⟨1,1,(1,0),(-5,4),(-4,8),2461⟩,
   ⟨1,1,(1,0),(-4,0),(-5,4),1622⟩,
   ⟨1,1,(1,0),(-4,0),(-1,-4),1622⟩,
   ⟨1,1,(1,0),(-4,8),(4,-8),21270⟩,
   ⟨1,1,(1,0),(-4,8),(-1,12),8968⟩,
   ⟨1,1,(1,0),(2,5),(7,7),5928⟩,
   ⟨0,5,(1,0),(-6,0),(-5,-2),5913⟩,
   ⟨0,5,(1,0),(-6,0),(-5,2),5913⟩,
   ⟨0,5,(1,0),(-5,2),(-2,4),8435⟩,
   ⟨0,6,(1,0),(-7,0),(-6,-2),9706⟩,
   ⟨0,6,(1,0),(-7,0),(-6,2),9706⟩,
   ⟨0,6,(1,0),(-6,2),(-3,4),13453⟩,
   ⟨1,2,(1,0),(-2,3),(1,5),1517⟩,
   ⟨1,2,(1,0),(1,5),(6,7),11143⟩,
   ⟨1,3,(1,0),(-4,1),(-3,-1),1451⟩,
   ⟨1,3,(1,0),(-4,1),(-3,3),1460⟩,
   ⟨1,3,(1,0),(-3,3),(0,5),3590⟩,
   ⟨1,4,(1,0),(-5,1),(-4,-1),3059⟩,
   ⟨1,4,(1,0),(-5,1),(-4,3),3090⟩,
   ⟨1,4,(1,0),(-4,3),(-1,5),6843⟩,
   ⟨1,5,(1,0),(-6,1),(-5,-1),5592⟩,
   ⟨1,5,(1,0),(-6,1),(-5,3),5661⟩,
   ⟨1,5,(1,0),(-5,3),(-2,5),11532⟩,
   ⟨1,6,(1,0),(-7,1),(-6,-1),9289⟩,
   ⟨1,6,(1,0),(-7,1),(-6,3),9415⟩,
   ⟨0,1,(1,1),(-1,-3),(-4,0),1281⟩,
   ⟨0,1,(1,1),(-1,-3),(4,-4),2561⟩,
   ⟨0,1,(1,1),(3,1),(8,4),6401⟩}

def OneSmallTripleRow.anchorA (r : OneSmallTripleRow) : QuadInt r.tau r.nu := ⟨r.a.1,r.a.2⟩
def OneSmallTripleRow.anchorB (r : OneSmallTripleRow) : QuadInt r.tau r.nu := ⟨r.b.1,r.b.2⟩
def OneSmallTripleRow.anchorS (r : OneSmallTripleRow) : QuadInt r.tau r.nu := ⟨r.s.1,r.s.2⟩



/-- The ordered finite row relation keeps the cutoff attached to its exact triple. -/
def OneSmallRowMembership {tau nu : ℤ} (a b s : QuadInt tau nu) (cutoff : ℤ) : Prop :=
  (⟨tau,nu,(a.re,a.im),(b.re,b.im),(s.re,s.im),cutoff⟩ : OneSmallTripleRow) ∈ oneSmallFixedRows

def OneSmallThirdRowProperty {tau nu : ℤ} (a b : QuadInt tau nu) : Prop :=
  ∀ s : QuadInt tau nu, s.norm ≤ 224 → b.norm ≤ s.norm → s ≠ a → s ≠ b →
    PairExtension a b s →
    (a = 1 ∧ b = -3 ∧ s = 3) ∨ ∃ cutoff, OneSmallRowMembership a b s cutoff

















































































end D1Bound5
end


