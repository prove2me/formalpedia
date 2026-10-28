-- Prove2me | Definitions.Def_Sensitivity213981Formal_MinmaxExpressions
-- name    : Sensitivity213981Formal_MinmaxExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T18:36:12.962804+00:00
-- url     : https://prove2.me/theorems/5982dd5e-58a8-4642-a02c-4d913dae8a00
-- title:
--   Minmax Expressions — sensitivity certificate definitions
-- statement:
--   The definitions for Minmax Expressions in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxNumeric.Entry.base`, `ThreeBoundMinmaxNumeric.rawBExpr`, `ThreeBoundMinmaxNumeric.primitiveMExpr`, `ThreeBoundMinmaxNumeric.pairMExpr`, `ThreeBoundMinmaxNumeric.rawMOriginalExpr`, `ThreeBoundMinmaxNumeric.rawMTierExpr`, `ThreeBoundMinmaxNumeric.rawMExpr`, `ThreeBoundMinmaxNumeric.rawPExpr`, `ThreeBoundMinmaxNumeric.Entry`, `ThreeBoundMinmaxNumeric.rawDExpr`, `ThreeBoundMinmaxNumeric.Entry.lowerAt`, `ThreeBoundMinmaxNumeric.rawExpr`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxExpressions.lean, lines 1–144.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Homogeneous numerical expressions for min/max B, M, P and D transfer.
Entries explicitly store all active tiers, including constant ordinary tiers. -/


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace ThreeBoundMinmaxNumeric
open ThreeBoundNumeric ThreeBoundFullProfile

structure Entry where
  lower : Array ℕ
  upper : Array ℕ
  guard : ℕ
  tolerance : ℕ
  deriving Inhabited, DecidableEq, Repr

def Entry.lowerAt (e : Entry) (d : ℕ) : ℕ := e.lower.getD d (e.lower.getD 0 0)
def Entry.upperAt (e : Entry) (d : ℕ) : ℕ := e.upper.getD d (e.upper.getD 0 0)

def Entry.plain (e : Entry) : Bool :=
  (List.range (e.tolerance+1)).all fun d => e.lowerAt d == e.upperAt d

def Entry.ordinary (e : Entry) : Bool :=
  (List.range (e.tolerance+1)).all fun d =>
    e.lowerAt d == e.lowerAt 0 && e.upperAt d == e.lowerAt 0

def Entry.same (e f : Entry) : Bool :=
  e.tolerance=f.tolerance ∧ e.guard=f.guard ∧
    ((List.range (e.tolerance+1)).all fun d =>
      e.lowerAt d == f.lowerAt d && e.upperAt d == f.upperAt d)

def Entry.base (e : Entry) : ThreeBoundNumeric.Entry :=
  ⟨e.lowerAt 0,e.lowerAt 1,e.lowerAt 2,e.guard,e.tolerance⟩

def rawBExpr (n degree : ℕ) (a c : Entry) : Expr n :=
  Expr.maximum ((List.range (c.tolerance+1)).map fun d =>
    let ti := a.lowerAt d
    let ui := a.upperAt d
    let tj := c.lowerAt d
    let uj := c.upperAt d
    max (bExpr n ti tj+bExpr n ti uj)
      (if tj< ui then bExpr n ui uj+minusExpr n ti tj ui else 0) +
    if a.tolerance ≤  d ∨ tj< a.lowerAt (d+1) ∨ uj< a.upperAt (d+1)
    then (degree-d)*aExpr n c.guard a.guard else 0)

def primitiveMExpr (n degree ti gi qi : ℕ) (j k : Entry) : Expr n :=
  ThreeBoundNumeric.primitiveMExpr n degree ti gi qi j.base k.base

def pairMExpr (n degree ti ui gi q tj uj gj tk uk gk : ℕ) : Expr n :=
  let a := aExpr n gj gi
  let m0 := minusExpr n ti tj tk
  let m1 := minusExpr n ui uj uk
  let b0 := bExpr n ti tk
  let b1 := bExpr n ui uk
  let target := max (if tj< tk ∧ uj< uk then m0+m1 else 0)
    (max (if tj< tk then m0+b1 else 0) (if uj< uk then b0+m1 else 0))
  max (if tj< tk ∨ uj< uk then target+(degree-q)*a else 0)
    (if gk< gj then b0+b1+(degree-q-1)*a+plusExpr n gk gj gi else 0)

/-- The ordinary upper-threshold component also applies when the weak entry is
not plain. This safely strengthens the previous plain-only fallback. -/
def rawMOriginalExpr (n degree : ℕ) (i j k : Entry) : Expr n :=
  if !j.ordinary ∨ !k.ordinary ∨ j.tolerance ≠ k.tolerance then rawBExpr n degree i j
  else if i.ordinary then primitiveMExpr n degree (i.lowerAt 0) i.guard i.tolerance j k
  else min (rawBExpr n degree i j)
    (primitiveMExpr n degree (i.upperAt j.tolerance) i.guard j.tolerance j k)

def rawMTierExpr (n degree : ℕ) (i j k : Entry) (d : ℕ) : Expr n :=
  let ti := i.lowerAt d
  let ui := i.upperAt d
  let tj := j.lowerAt d
  let uj := j.upperAt d
  let val := bExpr n ti tj+bExpr n ui uj+(degree-d)*aExpr n j.guard i.guard
  if d ≤  k.tolerance then min val (pairMExpr n degree ti ui i.guard d tj uj j.guard
    (k.lowerAt d) (k.upperAt d) k.guard) else val

def rawMExpr (n degree : ℕ) (i j k : Entry) : Expr n :=
  if j.same k then 0 else
    min (Expr.maximum ((List.range (j.tolerance+1)).map (rawMTierExpr n degree i j k)))
      (rawMOriginalExpr n degree i j k)

def rawPExpr (n pcross : ℕ) (rawA : Entry → Entry → Expr n) (j k l : Entry) : Expr n :=
  if j.same k then 0 else
    let first := rawA k l
    if j.tolerance=0 ∧ l.tolerance=0 ∧ j.plain ∧ k.plain ∧ l.plain then
      let tj := j.lowerAt 0
      let tk := k.lowerAt 0
      let tl := l.lowerAt 0
      let cross := pcross*aExpr n j.guard tl
      let m0 := minusExpr n l.guard tj tk
      let m1 := minusExpr n l.guard k.guard j.guard
      let basic := 2*bExpr n l.guard tj+cross+max (plusExpr n tj tk tl) m1
      let target := if tj< tk then cross+max (max (2*m0) (m0+bExpr n l.guard tk))
        (unionExpr n l.guard tj tk tl+bExpr n l.guard tl) else 0
      let guard := if k.guard< j.guard then cross+max (2*bExpr n l.guard tk)
        (2*bExpr n l.guard tl+m1) else 0
      min (min first basic) (max target guard)
    else first

/-- The oriented strict-D branch includes the earlier plain strict-D branch:
when all four pairs are plain its pairM term is the same primitive-M term. -/
def rawDExpr (n degree pcross : ℕ) (rawA : Entry → Entry → Expr n)
    (i j k l : Entry) : Expr n :=
  if j.same k then 0 else
    let first := rawMExpr n degree i j k+rawPExpr n pcross rawA j k l
    if j.tolerance=0 ∧ l.tolerance=0 ∧ l.plain ∧ k.upperAt 0 ≤  l.lowerAt 0 then
      let ti := i.lowerAt 0
      let ui := i.upperAt 0
      let tj := j.lowerAt 0
      let uj := j.upperAt 0
      let tk := k.lowerAt 0
      let uk := k.upperAt 0
      let tl := l.lowerAt 0
      let a := aExpr n l.guard i.guard
      min first (max (pairMExpr n degree ti ui i.guard 0 tj uj j.guard tk uk k.guard)
        (max (if tj< tk then bExpr n ui tl+degree*a+unionExpr n ti tj tk tl else 0)
          (if k.guard< j.guard then bExpr n ti tl+bExpr n ui tl+(degree-1)*a+
            unionExpr n l.guard k.guard j.guard i.guard else 0)))
    else first

def rawExpr (n degree pcross : ℕ) (rawA : Entry → Entry → Expr n)
    (recipe : Fin n → Entry) : Coord n → Expr n
  | .a i j => rawA (recipe i) (recipe j)
  | .b i j => rawBExpr n degree (recipe i) (recipe j)
  | .m i j => rawMExpr n degree (recipe i) (recipe j) (recipe (next j))
  | .p j l => rawPExpr n pcross rawA (recipe j) (recipe (next j)) (recipe l)
  | .d i j l => rawDExpr n degree pcross rawA (recipe i) (recipe j) (recipe (next j)) (recipe l)

def rawTransfer (n degree pcross : ℕ) (rawA : Entry → Entry → Expr n)
    (recipe : Fin n → Entry) (v : Profile n) : Profile n :=
  fun c => (rawExpr n degree pcross rawA recipe c).eval v



end ThreeBoundMinmaxNumeric



end
end Sensitivity213981Formal


