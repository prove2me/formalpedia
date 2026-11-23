-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqHermite251Midpoints
-- name    : GrothendieckLB_Supplement_cqHermite251Midpoints
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T21:27:19.522838+00:00
-- url     : https://prove2.me/theorems/9184f158-6b84-4961-a9fb-a0863331fcd5
-- title:
--   Midpoints for the degree-251 Hermite recurrence blocks
-- statement:
--   Each entry gives the two adjacent moment rows and the accumulated weights at the center of the corresponding recurrence block. These intermediate grid states allow a long exact calculation to be split into two separately verified inductions with a common boundary.
-- source:
--   Degree-251 fixed-point Hermite certificate for the cubic–quintic scheme of Saha et al., arXiv:2608.11158v2, and Prove2Me fc28e7f8-2588-498a-8ea6-e8d0e220ae2b.

import Definitions.Def_GrothendieckLB_Supplement_cqHermite251Checkpoints
import Mathlib.Tactic.Eval

namespace GrothendieckLB.Supplement.CQHermite251Mid
open CQHeadArithmetic CQDegree251
set_option maxRecDepth 150000
set_option exponentiation.threshold 50000
set_option maxHeartbeats 300000000



/-- Hermite row indices at which adjacent rows are retained. -/
def cuts : List ℕ := [4, 12, 20, 30, 40, 52, 64, 78, 92, 108, 125, 144, 165, 188, 213, 238]
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
  ⟨(pair i).1.toArray, (pair i).2.toArray, tab (cut i+1) CQHermite251.weightRow⟩

end GrothendieckLB.Supplement.CQHermite251Mid


