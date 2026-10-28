-- Prove2me | Definitions.Def_Sensitivity213303_Q2RawExpressions
-- name    : Sensitivity213303_Q2RawExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:20:07.003448+00:00
-- url     : https://prove2.me/theorems/6e290320-dd7b-4970-869f-b0b53e0e692e
-- title:
--   The exact q≤2 numerical transfer formulas
-- statement:
--   A recipe entry specifies target thresholds, guard level and tolerance. Caps stores ordinary and marked labeling cutoffs, and a Q2Record stores the finite high-head statistics. The formulas combine target-prefix caps, negative-target capacities, conditional head costs and external guard repairs to define raw A bounds; ordinary candidate cases cover larger tolerances. The same expression language defines the raw B, M, P and D bounds and the complete rawTransfer profile. Record admissibility conditions restrict the maximum to cases compatible with the particular weak/strong recipe pair.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module Q2RawExpressions; source SHA256 72bd65c86d9035aba99773f5119bbea179c21a9880b0d3982e3945fbcae7dba3.

/- Symbolic transcription of graded2_union_recurrence.py, with the ordinary
q=1, three-positive cap corrected to marked[6]+2, the established general
bound. This correction changes no coordinate of the first endpoint's four
numerical phases, because every ordinary q=1 fallback there is absent.
The formulas are homogeneous natural arithmetic expressions. This module
defines the numeric raw transfer; its semantic raw-A/M/P/D obligations are
separate theorems about the actual Boolean parent. -/
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ThreeBoundNumeric
open ThreeBoundFullProfile

instance _root_.ThreeBoundNumeric.instAddExpr_q2RawExpressions {n : ℕ} : Add (Expr n) := ⟨.add⟩
instance _root_.ThreeBoundNumeric.instSubExpr_q2RawExpressions {n : ℕ} : Sub (Expr n) := ⟨.sub⟩
instance _root_.ThreeBoundNumeric.instHMulNatExpr_q2RawExpressions {n : ℕ} : HMul ℕ (Expr n) (Expr n) := ⟨.scale⟩
instance _root_.ThreeBoundNumeric.instMinExpr_q2RawExpressions {n : ℕ} : Min (Expr n) := ⟨.min⟩
instance _root_.ThreeBoundNumeric.instMaxExpr_q2RawExpressions {n : ℕ} : Max (Expr n) := ⟨.max⟩
instance _root_.ThreeBoundNumeric.instOfNatExprOfNatNat_q2RawExpressions {n : ℕ} : OfNat (Expr n) 0 := ⟨.zero⟩








structure Caps where
  ordinary : Array ℕ
  guard : Array ℕ
  target : Array ℕ
  marked : Array ℕ
  zero : Array ℕ
  pcross : ℕ
  deriving Inhabited, Repr

def Caps.at (a : Array ℕ) (i : ℕ) : ℕ := a.getD i 0

structure Entry where
  t0 : ℕ
  t1 : ℕ
  t2 : ℕ
  guard : ℕ
  tolerance : ℕ
  deriving Inhabited, DecidableEq, Repr

def Entry.threshold (e : Entry) (k : ℕ) : ℕ :=
  if 3 ≤ e.tolerance ∨ k = 0 then e.t0 else if k = 1 then e.t1 else e.t2

def Entry.ordinary (e : Entry) : Bool :=
  3 ≤ e.tolerance ∨ e.tolerance = 0 ∨
    (e.t0 = e.t1 ∧ (e.tolerance = 1 ∨ e.t1 = e.t2))

def Entry.same (e f : Entry) : Bool :=
  e.tolerance = f.tolerance ∧ e.guard = f.guard ∧
    ((List.range (e.tolerance+1)).all fun k => e.threshold k == f.threshold k)

abbrev Q2Record := ℕ → ℕ
def recordOfList (xs : List ℕ) : Q2Record := fun i => xs[i]?.getD 0

def kindBudget (t : ℕ) : ℕ :=
  match t with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 1 | 4 => 2 | 5 => 3 | 6 => 1 | _ => 2

def positiveInside (t q : ℕ) : Bool :=
  (t ≤ 2 ∧ t ≤ q) ∨ (t = 6 ∧ 1 ≤ q) ∨ (t = 7 ∧ 2 ≤ q)

def positiveCount (x : Q2Record) (k : ℕ) : ℕ :=
  if k = 0 then x 0 else if k = 1 then x 1+x 6 else x 2+x 7

def positivePrefix (x : Q2Record) (q : ℕ) : ℕ :=
  ((List.range (q+1)).map (positiveCount x)).sum

def headCount (x : Q2Record) : ℕ := ((List.range 8).map x).sum

def capPrefix (caps : Caps) (x : Q2Record) (q : ℕ) : ℕ := Id.run do
  let low := ((List.range 8).filterMap fun t =>
    if !positiveInside t q ∧ kindBudget t ≤ q then some (x t) else none).sum
  let nxt := ((List.range 8).filterMap fun t =>
    if !positiveInside t q ∧ kindBudget t ≤ q+1 then some (x t) else none).sum
  let eligible := ((List.range 8).filterMap fun t =>
    if kindBudget t ≤ q+1 then some (x t) else none).sum
  let outside := nxt
  let mut cap := min (Caps.at caps.ordinary q - 1 - low) (Caps.at caps.ordinary q - nxt)
  let nh := headCount x
  let up := positivePrefix x q
  if q = 0 then
    if 1 ≤ nh then cap := min cap (x 0+caps.pcross+x 25)
    if 2 ≤ nh then cap := min cap (x 0+Caps.at caps.zero 2+x 26)
  else
    if 1 ≤ eligible then cap := min cap (Caps.at caps.marked (q-1)-1+(1-outside))
    if 2 ≤ eligible then cap := min cap (Caps.at caps.marked (if q=1 then 4 else 5)-1+(2-outside))
    if q=1 ∧ 3 ≤ nh then cap := min cap (up+Caps.at caps.marked 6-1+x 27)
    if q=2 ∧ 4 ≤ nh then cap := min cap (up+Caps.at caps.marked 7-1+x 28)
  return cap

def allowedRecord (caps : Caps) (q : ℕ) (x : Q2Record) : Bool :=
  (!(q == 1) || (x 2 == 0 && x 5 == 0 && x 7 == 0)) &&
  (List.range (q+1)).all fun k => positivePrefix x k ≤ capPrefix caps x k

def suffixCapacity (caps : Caps) (q : ℕ) (x : Q2Record) (k : ℕ) : ℕ :=
  ((interval k (q+1)).map fun j => capPrefix caps x j-positivePrefix x j).foldl min
    (capPrefix caps x q-positivePrefix x q)

def negativeCount (caps : Caps) (q : ℕ) (x : Q2Record) (k : ℕ) : ℕ :=
  if k=0 then suffixCapacity caps q x 0 else
    suffixCapacity caps q x k-suffixCapacity caps q x (k-1)

structure OrdinaryCase where
  positive : ℕ
  target : ℕ
  external : ℕ
  internal : ℕ
  low : ℕ
  save : ℕ
  cap : ℕ
  deriving Inhabited, Repr

def markedIndex (q m : ℕ) : Option ℕ :=
  match q,m with
  | 1,3 => some 6 | 2,4 => some 7 | 3,5 => some 8
  | 3,6 => some 9 | 4,6 => some 10 | 3,7 => some 11 | _,_ => none

def ordinaryCase (caps : Caps) (q m u : ℕ) : Option OrdinaryCase := Id.run do
  let e := m*(m-1)/2
  let ext := m*(q+1)-e
  let intr := min e (2*m)
  let t := if 0 < m then min (Caps.at caps.ordinary q-m) (Caps.at caps.guard q) else Caps.at caps.ordinary q-1
  if q*u+(q+1)*m < (u+m)*(u+m-1)/2 then return none
  let mut tt := if 0 < u then min t (Caps.at caps.target q) else t
  if q=1 ∧ 2≤u then tt := min tt (Caps.at caps.marked 0-1)
  if q=1 ∧ 3≤u then tt := min tt (Caps.at caps.marked 6+2)
  if q=1 ∧ 2≤ m then tt := min tt (Caps.at caps.marked 4-1)
  if q=2 ∧ 2≤ m then tt := min tt (Caps.at caps.marked 5-1)
  if tt < u then return none
  let low := u*m+u*(u-1)/2-u*q
  let cap := match markedIndex q m with
    | some i => Caps.at caps.marked i-1
    | none => 1000000000
  return some ⟨u,tt,ext,intr,low,low-u,cap⟩

def ordinaryCases (caps : Caps) (q : ℕ) (same : Bool) : List OrdinaryCase :=
  (List.range ((if same then 2*q+3 else 0)+1)).flatMap fun m =>
    (List.range (2*q+2)).filterMap (ordinaryCase caps q m)

def ordinaryAExpr (n : ℕ) (caps : Caps) (ta ga qa tb gb q : ℕ) : Expr n :=
  let a := plusExpr n gb ta tb
  let b := aExpr n gb tb
  let s := bExpr n gb ga
  let j := bExpr n gb tb
  if q = 0 then
    let z := max (Caps.at caps.zero 0*b) (a+Caps.at caps.zero 1*b)
    if qa ≠ 0 then z else Expr.maximum [z,
      Caps.at caps.zero 2*b+max (min (a+s) (unionExpr n gb ga ta tb)) (a+j),
      Caps.at caps.zero 3*b+s,Caps.at caps.zero 4*b+j,Caps.at caps.zero 5*b+s+j,
      Caps.at caps.zero 6*b+2*j,Caps.at caps.zero 7*b+3*j]
  else Expr.maximum ((ordinaryCases caps q (qa == q)).map fun c =>
    if 0 < c.positive ∧ gb = ta then 0 else
      let t := c.target-c.positive
      let ext := c.external-c.save
      let intr := c.internal+min c.positive c.save
      let budget := c.external-c.low
      let k := min c.cap t
      let extra := min t (k+budget)-k
      c.positive*a+max (k*b+ext*s+intr*j)
        ((k+extra)*b+(ext-extra)*s+(intr+extra)*j))

def headCost (n : ℕ) (a c : Entry) (t h : ℕ) : Expr n :=
  let q := c.tolerance
  let gi := a.guard
  let gj := c.guard
  if t ≤ 2 then
    let k := t
    let weak := a.threshold k
    let strong := c.threshold k
    let barrier := if k = 0 then weak else min weak (c.threshold (k-1))
    let ap := plusExpr n gj barrier strong
    let ss := bExpr n gj gi
    let u := min (unionExpr n gj gi barrier strong) (ap+ss)
    let j := bExpr n gj strong
    if h=0 then ap else if h=1 then max u (ap+j) else j+max u ap
  else if t ≤ 5 then
    let k := t-3
    let strong := c.threshold k
    if k < q then
      let nxt := c.threshold (k+1)
      let weakNext := a.threshold (k+1)
      let m := minusExpr n gj strong nxt
      let low := minusExpr n gj strong weakNext
      let middle := minusExpr n gj weakNext nxt
      if h=0 then 0 else if h=1 then min m (max low middle)
        else min (2*m) (max (2*low) (low+middle))
    else if h=0 then 0 else h*bExpr n gj strong
  else
    let k := t-5
    let prev := c.threshold (k-1)
    let weak := a.threshold k
    let strong := c.threshold k
    let u₀ := unionExpr n gj prev weak strong
    let ap := min (plusExpr n prev weak strong) u₀
    let u := min u₀ (ap+minusExpr n gj prev weak)
    let j := bExpr n gj strong
    if h=0 then ap else if h=1 then max u (ap+j) else u+j

def recordAllowedFor (caps : Caps) (a c : Entry) (x : Q2Record) : Bool :=
  allowedRecord caps c.tolerance x &&
    (List.range (c.tolerance+1)).all (fun k =>
      !(k < a.tolerance ∧ a.threshold (k+1) ≤ c.threshold k) ||
        (x (3+k) == 0 && (if k=0 then x 6 == 0 else if k=1 then x 7 == 0 else true))) &&
    (List.range (c.tolerance+1)).all (fun k => x k == 0 ||
      !(c.guard == (if k=0 then a.threshold k else min (a.threshold k) (c.threshold (k-1)))))

def recordCost (n : ℕ) (caps : Caps) (a c : Entry) (x : Q2Record) : Expr n :=
  x 8 * bExpr n c.guard a.guard +
  Expr.sum ((List.range (c.tolerance+1)).map fun k =>
    negativeCount caps c.tolerance x k * aExpr n c.guard (c.threshold k)) +
  Expr.sum ((List.range 8).map fun t =>
    x t * headCost n a c t 0 +
    x (9+2*t) * (headCost n a c t 1-headCost n a c t 0) +
    x (10+2*t) * (headCost n a c t 2-headCost n a c t 0))

def rawAExpr (n : ℕ) (caps : Caps) (records : List (List ℕ))
    (a c : Entry) : Expr n :=
  let qi := a.tolerance
  let q := c.tolerance
  if q=0 then ordinaryAExpr n caps a.t0 a.guard
    (if 1 ≤ qi ∧ a.threshold 1 ≤ c.t0 then 1 else 0) c.t0 c.guard 0
  else if 3 ≤ q then ordinaryAExpr n caps a.t0 a.guard qi c.t0 c.guard q
  else
    let first := Expr.maximum (records.filterMap fun xs =>
      let x := recordOfList xs
      if recordAllowedFor caps a c x then some (recordCost n caps a c x) else none)
    if c.ordinary then
      Expr.minimum first ((interval q (qi+1)).filterMap fun level =>
        if a.threshold level ≤ c.t0 then
          some (ordinaryAExpr n caps (a.threshold level) a.guard level c.t0 c.guard q)
        else none)
    else first

def rawBExpr (n degree : ℕ) (a c : Entry) : Expr n :=
  Expr.maximum ((List.range (c.tolerance+1)).map fun d =>
    2*bExpr n (a.threshold d) (c.threshold d)+
      if a.tolerance ≤ d ∨ c.threshold d < a.threshold (d+1)
      then (degree-d)*aExpr n c.guard a.guard else 0)

def primitiveMExpr (n degree ti gi qi : ℕ) (j k : Entry) : Expr n :=
  let q := j.tolerance
  let aa := aExpr n j.guard gi
  let mt := minusExpr n ti j.t0 k.t0
  max (if j.t0 < k.t0 then max (2*mt) (mt+bExpr n ti k.t0)+
      (if qi=q then (degree-q)*aa else 0) else 0)
    (if k.guard < j.guard then 2*bExpr n ti k.t0+
      (if qi=q then (degree-q-1)*aa+plusExpr n k.guard j.guard gi else 0) else 0)

def rawMExpr (n degree : ℕ) (i j k : Entry) : Expr n :=
  if j.same k then 0 else
    if !j.ordinary ∨ !k.ordinary ∨ j.tolerance ≠ k.tolerance then rawBExpr n degree i j
    else if i.ordinary then primitiveMExpr n degree i.t0 i.guard i.tolerance j k
    else min (rawBExpr n degree i j)
      (primitiveMExpr n degree (i.threshold j.tolerance) i.guard j.tolerance j k)

def rawPExpr (n degree : ℕ) (caps : Caps) (records : List (List ℕ))
    (j k l : Entry) : Expr n :=
  if j.same k then 0 else
    let first := rawAExpr n caps records k l
    if j.tolerance=0 ∧ l.tolerance=0 then
      let cross := caps.pcross*aExpr n j.guard l.t0
      let m₀ := minusExpr n l.guard j.t0 k.t0
      let m₁ := minusExpr n l.guard k.guard j.guard
      let z₁ := 2*bExpr n l.guard j.t0+cross+max (plusExpr n j.t0 k.t0 l.t0) m₁
      let target := if j.t0 < k.t0 then cross+Expr.maximum [2*m₀,
        m₀+bExpr n l.guard k.t0,unionExpr n l.guard j.t0 k.t0 l.t0+bExpr n l.guard l.t0] else 0
      let guard := if k.guard < j.guard then cross+max (2*bExpr n l.guard k.t0)
        (2*bExpr n l.guard l.t0+m₁) else 0
      min (min first z₁) (max target guard)
    else first

def rawDExpr (n degree : ℕ) (caps : Caps) (records : List (List ℕ))
    (i j k l : Entry) : Expr n :=
  let first := rawMExpr n degree i j k + rawPExpr n degree caps records j k l
  if j.tolerance=0 ∧ l.tolerance=0 then
    let strict := if j.same k then 0 else
      let bb := bExpr n i.t0 l.t0
      let aa := aExpr n l.guard i.guard
      Expr.maximum [primitiveMExpr n degree i.t0 i.guard 0 j k,
        if j.t0 < k.t0 then bb+degree*aa+unionExpr n i.t0 j.t0 k.t0 l.t0 else 0,
        if k.guard < j.guard then 2*bb+(degree-1)*aa+
          unionExpr n l.guard k.guard j.guard i.guard else 0]
    min first strict
  else first

def rawExpr (n degree : ℕ) (caps : Caps) (records : List (List ℕ))
    (recipe : Fin n → Entry) : Coord n → Expr n
  | .a i j => rawAExpr n caps records (recipe i) (recipe j)
  | .b i j => rawBExpr n degree (recipe i) (recipe j)
  | .m i j => rawMExpr n degree (recipe i) (recipe j) (recipe (next j))
  | .p j l => rawPExpr n degree caps records (recipe j) (recipe (next j)) (recipe l)
  | .d i j l => rawDExpr n degree caps records (recipe i) (recipe j) (recipe (next j)) (recipe l)

def rawTransfer (n degree : ℕ) (caps : Caps) (records : List (List ℕ))
    (recipe : Fin n → Entry) (v : Profile n) : Profile n :=
  fun c => (rawExpr n degree caps records recipe c).eval v



end ThreeBoundNumeric


