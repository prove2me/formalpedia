-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxAExpressions
-- name    : BS2_b3ba934b_MinmaxAExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:26:31.634318+00:00
-- url     : https://prove2.me/theorems/e3ea5b78-daeb-4b8b-b73a-ddc356190426
-- title:
--   Sensitivity separation: MinmaxAExpressions (complete source module)
-- statement:
--   Complete Lean source module `MinmaxAExpressions` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxAExpressions.lean; original SHA-256 f8e074297a81223739aefdea9e5c61c5a44892f663c15f44bb9c4fd599e34552; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact min/max upward cost with the shared full q2 record table. -/
import Definitions.Def_BS2_b3ba934b_MinmaxExpressions

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxA
open ThreeBoundNumeric ThreeBoundFullProfile

def positiveExpr (n : ℕ) (a c : ThreeBoundMinmaxNumeric.Entry) (b : ℕ) : Expr n :=
  max (plusExpr n c.guard (a.lowerAt b) (c.lowerAt b))
    (max (plusExpr n c.guard (a.upperAt b) (c.upperAt b))
      (2*plusExpr n (c.lowerAt b) (a.upperAt b) (c.upperAt b)))

def targetCost (n : ℕ) (a c : ThreeBoundMinmaxNumeric.Entry) (k : ℕ) : Expr n :=
  if k ≤ 2 then positiveExpr n a c k else
    if 6 ≤ k then positiveExpr n a c (k-5) else 0

def guardCost (n : ℕ) (a c : ThreeBoundMinmaxNumeric.Entry) (k h : ℕ) : Expr n :=
  if k ≤ 2 then h*bExpr n c.guard a.guard else
    let b := if k ≤ 5 then k-3 else k-6
    if h=0 then 0 else if h=1 then bExpr n c.guard (c.lowerAt b) else
      bExpr n c.guard (c.lowerAt b)+bExpr n c.guard (c.upperAt b)

def headCost (n : ℕ) (a c : ThreeBoundMinmaxNumeric.Entry) (k h : ℕ) : Expr n :=
  targetCost n a c k+guardCost n a c k h

def negativeExpr (n : ℕ) (caps : Caps) (c : ThreeBoundMinmaxNumeric.Entry) (r : Q2Record) : Expr n :=
  Expr.sum ((List.range (c.tolerance+1)).map fun b =>
    negativeCount caps c.tolerance r b*aExpr n c.guard (c.lowerAt b))

def highExpr (n : ℕ) (a c : ThreeBoundMinmaxNumeric.Entry) (r : Q2Record) : Expr n :=
  Expr.sum ((List.range 8).map fun k =>
    r k*headCost n a c k 0+
    r (9+2*k)*(headCost n a c k 1-headCost n a c k 0)+
    r (10+2*k)*(headCost n a c k 2-headCost n a c k 0))

def recordCost (n : ℕ) (caps : Caps) (a c : ThreeBoundMinmaxNumeric.Entry) (r : Q2Record) : Expr n :=
  r 8*bExpr n c.guard a.guard+negativeExpr n caps c r+highExpr n a c r

def recordAllowedFor (caps : Caps) (a c : ThreeBoundMinmaxNumeric.Entry) (r : Q2Record) : Bool :=
  allowedRecord caps c.tolerance r &&
    (List.range (c.tolerance+1)).all (fun b =>
      !(b < a.tolerance ∧ a.lowerAt (b+1) ≤ c.lowerAt b ∧ a.upperAt (b+1) ≤ c.upperAt b) ||
        (r (3+b)==0 && (if b=0 then r 6==0 else if b=1 then r 7==0 else true))) &&
    (List.range (c.tolerance+1)).all (fun b =>
      r b==0 || !(c.guard==a.lowerAt b && c.guard==a.upperAt b))

def gradedAExpr (n : ℕ) (caps : Caps) (records : List (List ℕ)) (a c : ThreeBoundMinmaxNumeric.Entry) : Expr n :=
  Expr.maximum (records.filterMap fun xs =>
    let r := recordOfList xs
    if recordAllowedFor caps a c r then some (recordCost n caps a c r) else none)

def zeroAExpr (n : ℕ) (caps : Caps) (a c : ThreeBoundMinmaxNumeric.Entry) : Expr n :=
  let ti := a.lowerAt 0
  let ui := a.upperAt 0
  let tj := c.lowerAt 0
  let uj := c.upperAt 0
  let ap := plusExpr n c.guard ti tj
  let au := plusExpr n c.guard ui uj
  let a2 := plusExpr n tj ui uj
  let b := aExpr n c.guard tj
  let bu := aExpr n c.guard uj
  let s := bExpr n c.guard a.guard
  let j := bExpr n c.guard tj
  let ju := bExpr n c.guard uj
  let first := max (Caps.at caps.zero 0*b) (Caps.at caps.zero 1*b+positiveExpr n a c 0)
  if 1 ≤ a.tolerance ∧ a.lowerAt 1 ≤ tj ∧ a.upperAt 1 ≤ uj then first else
    let cross := max (b+ju) (bu+j)
    let high := max (min (ap+s) (unionExpr n c.guard a.guard ti tj))
      (max (min (au+s) (unionExpr n c.guard a.guard ui uj))
        (max (ap+ju) (max (au+j) (unionExpr n c.guard tj ui uj+a2))))
    Expr.maximum [first,Caps.at caps.zero 2*b+high,
      Caps.at caps.zero 3*b+s,Caps.at caps.zero 3*b+cross,
      Caps.at caps.zero 5*b+s+j,Caps.at caps.zero 5*b+cross+j,Caps.at caps.zero 7*b+3*j]

def rawAExpr (n : ℕ) (caps : Caps) (records : List (List ℕ)) (a c : ThreeBoundMinmaxNumeric.Entry) : Expr n :=
  if a.plain && c.plain then ThreeBoundNumeric.rawAExpr n caps records a.base c.base
  else if c.tolerance=0 then zeroAExpr n caps a c
  else
    let first := gradedAExpr n caps records a c
    if c.ordinary then
      Expr.minimum first ((interval c.tolerance (a.tolerance+1)).filterMap fun b =>
        if a.upperAt b ≤ c.lowerAt 0 then
          some (ordinaryAExpr n caps (a.upperAt b) a.guard b (c.lowerAt 0) c.guard c.tolerance)
        else none)
    else first

end ThreeBoundMinmaxA


