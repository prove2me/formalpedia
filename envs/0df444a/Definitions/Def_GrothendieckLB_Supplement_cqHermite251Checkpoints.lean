-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqHermite251Checkpoints
-- name    : GrothendieckLB_Supplement_cqHermite251Checkpoints
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T20:42:00.599688+00:00
-- url     : https://prove2.me/theorems/de22c305-63a9-494a-8ef9-caf545ed2a80
-- title:
--   Integer checkpoint rows for the degree-251 Hermite recurrence
-- statement:
--   Seventeen selected pairs of adjacent moment rows partition the Hermite calculation at cutoff 251. Each entry is an explicit six-tuple of integer endpoints. A checkpoint state consists of its two moment rows and the prefix of the packed Hermite weight table through its index. These witnesses allow independently checked blocks to be combined by induction.
-- source:
--   Degree-251 fixed-point Hermite certificate for the cubic–quintic scheme of Saha et al., arXiv:2608.11158v2, and Prove2Me fc28e7f8-2588-498a-8ea6-e8d0e220ae2b.

import Definitions.Def_GrothendieckLB_Supplement_cqDegree251Tables
import Mathlib.Tactic.Eval

namespace GrothendieckLB.Supplement.CQHermite251
open CQHeadArithmetic CQDegree251
set_option maxRecDepth 150000
set_option exponentiation.threshold 50000
set_option maxHeartbeats 300000000

deriving instance Lean.ToExpr for Interval
deriving instance Lean.ToExpr for MomentCombination

/-- Hermite row indices at which adjacent rows are retained. -/
def cuts : List ℕ := [0, 8, 16, 25, 35, 46, 58, 71, 85, 100, 116, 134, 154, 176, 200, 226, 251]
def cut (i : ℕ) := cuts[i]?.getD 0

private def initFast (N : Nat) (raw : Array MomentCombination) : Array MomentCombination := Id.run do
  let len := 3*N+1
  let mut fact := #[1]
  let mut dbl := #[1,1]
  for i in [:len] do
    fact := fact.push ((i+1)*fact[i]!)
    dbl := dbl.push ((i+2)*dbl[i]!)
  let mut ini := #[]
  for b in [:len] do
    let mut sum := zeroCombination
    if b%2=0 then
      for t in [:b/2+1] do
        let k := 2*t
        let d := b-k
        let mag : Nat := dbl[d-1]! * (fact[b]! / (fact[k]! * fact[d]!))
        let coeff : Int := if d%4 = 0 then mag else -(mag:Int)
        sum := addCombination sum (scaleCombination coeff raw[k]!)
    ini := ini.push sum
  return ini


/-- Compute the moment rows in one pass, retaining only the specified pairs. -/
private def sample (N : ℕ) : List (List MomentCombination × List MomentCombination) := Id.run do
  let raw := momentRows (3*N-5)
  let mut cur := initFast N raw
  let mut prev := cur
  let mut pairs := #[]
  for p in [:N+1] do
    if cuts.contains p then pairs := pairs.push (prev.toList, cur.toList)
    let next := nextRow p prev cur
    prev := cur
    cur := next
  return pairs.toList

/-- Numerical values used as witnesses at the boundaries of successive recurrence blocks. -/
noncomputable def pairs : List (List MomentCombination × List MomentCombination) := eval% (sample 251)

noncomputable def pair (i : ℕ) := pairs[i]?.getD ([],[])
noncomputable def weightRow (a : ℕ) := wrow (entry default wp a) (252-a)

/-- The complete grid at a checkpoint, using decoded weights from all preceding rows. -/
noncomputable def state (i : ℕ) : Grid :=
  ⟨(pair i).1.toArray, (pair i).2.toArray, tab (cut i+1) weightRow⟩

end GrothendieckLB.Supplement.CQHermite251


