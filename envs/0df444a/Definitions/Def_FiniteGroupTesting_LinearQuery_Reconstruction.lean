-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_Reconstruction
-- name    : FiniteGroupTesting_LinearQuery_Reconstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:48.2502+00:00
-- url     : https://prove2.me/theorems/d137a1b4-bdbb-42f2-9658-d17c7bc23b0a
-- title:
--   Identity verification and group reconstruction
-- statement:
--   Choose the first label $a$. Query $a*x$ and $x*a$ for every label, require exactly one $e$ with both products equal to $a$, and verify $e*x=x*e=x$ globally. Start with $H=\{e\}$ and no generators. Choose each next $b$ deterministically by scanning missing labels, run Algorithm 1 and the regularity test, and reject on either failure.
--
--   $$L=\lceil\log_2n\rceil,\qquad \delta_{\rm reg}=\frac1{100L},\qquad r=\lceil\log_2(100L)\rceil.$$
--
--   At most $L$ extension calls are allowed. Accepted actions remain raw stored tables: nonregular actions mistakenly accepted by the test are retained as possible executions. No correctness invariant is placed in an output constructor. Array initialization and integer round-count setup are charged.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 22–23, §3.3

import Definitions.Def_FiniteGroupTesting_LinearQuery_RegularityProgram

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Index lookup on the supplied positive labelled carrier; only the valid range is scanned. -/
def labelAt {n : ℕ} (fallback : Fin n) (i : ℕ) : Fin n :=
  if hi : i < n then ⟨i, hi⟩ else fallback

def identityCandidates {n : ℕ} (a : Fin n) :
    ℕ → ℕ → Fin n → OracleRun n (ℕ × Fin n)
  | 0, count, candidate => pure (count, candidate)
  | j + 1, count, candidate => do
      charge 10
      let x := labelAt a (n - (j + 1))
      let ax ← ask a x
      let xa ← ask x a
      if ax == a && xa == a then
        identityCandidates a j (count + 1) x
      else identityCandidates a j count candidate

def verifyIdentity {n : ℕ} (e : Fin n) : ℕ → OracleRun n Bool
  | 0 => pure true
  | j + 1 => do
      charge 8
      let x := labelAt e (n - (j + 1))
      let ex ← ask e x
      let xe ← ask x e
      if ex != x || xe != x then return false
      verifyIdentity e j

def identityProgram {n : ℕ} (a : Fin n) : OracleRun n (Option (Fin n)) := do
  let (count, e) ← identityCandidates a n 0 a
  charge 4
  if count != 1 then return none
  let good ← verifyIdentity e n
  return if good then some e else none

def chooseMissing {n : ℕ} (a : StoredAction n) (e : Fin n) : ℕ → OracleRun n (Fin n)
  | 0 => pure e
  | j + 1 => do
      charge 6
      let b := labelAt e (n - (j + 1))
      if !a.domain.marked b then return b
      chooseMissing a e j

def singletonAction {n : ℕ} (e : Fin n) : StoredAction n :=
  ⟨(LabelSet.empty e).insert e, 0, fun _ => id⟩

/-- At most L extensions; no regularity promise is imposed on accepted intermediate states. -/
def reconstructionLoop {n : ℕ} (e : Fin n) (r : ℕ) :
    ℕ → StoredAction n → OracleRun n (Option (StoredAction n))
  | 0, a => .step 4 (.done (if a.domain.count == n then some a else none))
  | fuel + 1, a => do
      charge 6
      if a.domain.count == n then return some a
      let b ← chooseMissing a e n
      let result ← exploreExtension a e b
      match result with
      | none => return none
      | some out =>
          let good ← regularityProgram out.action e r
          if !good then return none
          reconstructionLoop e r fuel out.action

/-- Section 3.3, with r = ceil(log_2(100 L)) and delta_reg = 1/(100 L). -/
def reconstruction {n : ℕ} (e : Fin n) : OracleRun n (Option (StoredAction n)) := do
  let L ← ceilLogProgram n
  let r ← ceilLogProgram (100 * L)
  charge (6 * n + 6)
  reconstructionLoop e r L (singletonAction e)

end FiniteGroupTesting.LinearQuery


