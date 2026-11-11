-- Prove2me | Definitions.Def_RoundedPotentials_Main_Verifier
-- name    : RoundedPotentials_Main_Verifier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T08:33:57.867209+00:00
-- url     : https://prove2.me/theorems/f34b253f-451d-473b-bd77-61cdf7c004f6
-- title:
--   The p.17 integer verifier with primitive operation and magnitude counters
-- statement:
--   The certificate input is a list of signed integer indices, with no supplied flow or cut. For $Q=32n^2W$, the verifier rejects a claim outside $0\le p\le(n-1)W$, then reads exactly $n$ indices, rejecting any outside $[0,(2n-1)Q]$. Its bounded parser examines at most $n$ entries and one additional list constructor, so a very long rejected suffix is never scanned. It checks the two scaled intervals and terminal inequalities.
--
--   Starting with zero integer counters, it processes each listed edge $u\to v$ with
--   $$F_{uv}=c_{uv}\min(Q,\max(0,i_u-i_v)),\qquad E_u\gets E_u+F_{uv},\quad E_v\gets E_v-F_{uv}.$$
--   It finally accepts exactly when $|E_v-Qp(1[v=s]-1[v=t])|\le4nW=Q/(8n)$ at every vertex.
--
--   Every integer addition, subtraction, multiplication, absolute value, and comparison goes through a primitive that increments the operation counter and records operand and result magnitudes. Clipping uses two counted comparisons. The initial two range comparisons for each raw index and the raw claim are counted, but their untrusted operand is exempt from the word-size statistic. Their bounds and Boolean results are recorded. After a successful range check, all subsequent operands and results are recorded. This explicit exception allows rejection of arbitrarily large inputs without claiming they already fit a bounded word.
--
--   Array reads/writes, list constructors, structural iteration, type-level indexing, and instrumentation are the RAM bookkeeping convention, rather than integer arithmetic. The verifier uses constant-time RAM arrays for indices and excess counters. Terminal identity tests in the final loop use four counted integer comparisons. Typed integer lists abstract canonical integer decoding; malformed lengths, negative entries, oversized entries and invalid interval membership are rejected by the actual program.
--
--   Only these primitives produce the statistics; the verifier computes its Boolean result without a maximum-flow predicate or oracle.
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 17, Proof of Theorem 1.1; p. 12, Definition 2.3 (all guesses must terminate within the bound)

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Certificate

namespace RoundedPotentials.Main

/-- Ghost instrumentation. Only the primitives below update this state. -/
structure Meter where
  ops : ℕ := 0
  maxAbs : ℕ := 0
  deriving Repr, DecidableEq

abbrev Counted := StateM Meter

/-- One integer arithmetic operation or comparison, with operands and result recorded. -/
def charge (a b z : ℤ) : Counted Unit :=
  modify fun st => ⟨st.ops + 1, max st.maxAbs (max a.natAbs (max b.natAbs z.natAbs))⟩

def iadd (a b : ℤ) : Counted ℤ := do
  let z := a + b
  charge a b z
  return z

def isub (a b : ℤ) : Counted ℤ := do
  let z := a - b
  charge a b z
  return z

def imul (a b : ℤ) : Counted ℤ := do
  let z := a * b
  charge a b z
  return z

def ile (a b : ℤ) : Counted Bool := do
  let z := decide (a ≤ b)
  charge a b (if z then 1 else 0)
  return z

def iabs (a : ℤ) : Counted ℤ := do
  let z := |a|
  charge a 0 z
  return z

/-- The two RAW input-range comparisons are counted, but the untrusted operand is exempt
from the word-size statistic. No arithmetic is performed on that operand before this guard. -/
def inputRange (x bound : ℤ) : Counted Bool := do
  let lo := decide (0 ≤ x)
  let hi := decide (x ≤ bound)
  charge 0 0 (if lo then 1 else 0)
  charge bound 0 (if hi then 1 else 0)
  return lo && hi

/-- Bounded parser: examines at most n fields and one end-of-list constructor.
Overlong lists are rejected without computing their length or examining their suffix. -/
def readIndices : ℕ → List ℤ → Array ℤ → ℤ → Counted (Option (Array ℤ))
  | 0, [], acc, _ => pure (some acc)
  | 0, _ :: _, _, _ => pure none
  | _ + 1, [], _, _ => pure none
  | k + 1, x :: xs, acc, bound => do
      if ← inputRange x bound then readIndices k xs (acc.push x) bound else return none

def iclip (x q : ℤ) : Counted ℤ := do
  let z ← if ← ile x 0 then pure 0 else pure x
  if ← ile q z then return q else return z

/-- Constant time RAM reads/writes and structural traversal are not integer arithmetic.
Every numeric test, clipping test, and arithmetic calculation uses a counted primitive. -/
def verifyProgram {n W : ℕ} (I : Instance n W) (s t : Fin n)
    (p : ℤ) (certificate : List ℤ) : Counted Bool := do
  let nv : ℤ := n
  let wv : ℤ := W
  let nm ← isub nv 1
  let q1 ← imul 32 nv
  let q2 ← imul q1 nv
  let q ← imul q2 wv
  let low ← imul nm q
  let nq ← imul nv q
  let tn ← imul 2 nv
  let tnm ← isub tn 1
  let upper ← imul tnm q
  let pmax ← imul nm wv
  let tol1 ← imul 4 nv
  let tol ← imul tol1 wv
  if !(← inputRange p pmax) then return false
  let parsed ← readIndices n certificate #[] upper
  match parsed with
  | none => return false
  | some indices =>
    for v in List.finRange n do
      let x := (indices.getD v.val 0)
      let lowerInterval ← ile x low
      let upperInterval ← ile nq x
      if !(lowerInterval || upperInterval) then return false
    if !(← ile nq ((indices.getD s.val 0))) then return false
    if !(← ile ((indices.getD t.val 0)) low) then return false
    let mut counters : Array ℤ := Array.replicate n 0
    for e in I.edges do
      let drop ← isub ((indices.getD e.1.val 0)) ((indices.getD e.2.1.val 0))
      let clipped ← iclip drop q
      let amount ← imul (e.2.2 : ℤ) clipped
      let eu ← iadd ((counters.getD e.1.val 0)) amount
      counters := counters.set! e.1.val eu
      let ev ← isub ((counters.getD e.2.1.val 0)) amount
      counters := counters.set! e.2.1.val ev
    let qp ← imul q p
    let negqp ← isub 0 qp
    for v in List.finRange n do
      -- Terminal identity comparisons are also charged.
      let atS ← ile (v.val : ℤ) (s.val : ℤ)
      let fromS ← ile (s.val : ℤ) (v.val : ℤ)
      let atT ← ile (v.val : ℤ) (t.val : ℤ)
      let fromT ← ile (t.val : ℤ) (v.val : ℤ)
      let b := if atS && fromS then qp else if atT && fromT then negqp else 0
      let err ← isub ((counters.getD v.val 0)) b
      let magnitude ← iabs err
      if !(← ile magnitude tol) then return false
    return true

def verify {n W : ℕ} (I : Instance n W) (s t : Fin n)
    (p : ℤ) (certificate : List ℤ) : Bool × Meter :=
  (verifyProgram I s t p certificate).run ⟨0, 0⟩

end RoundedPotentials.Main


