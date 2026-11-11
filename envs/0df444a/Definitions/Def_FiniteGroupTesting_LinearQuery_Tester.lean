-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_Tester
-- name    : FiniteGroupTesting_LinearQuery_Tester
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:08:08.856835+00:00
-- url     : https://prove2.me/theorems/5e99e4b6-29a1-475e-b351-34876a317d3d
-- title:
--   The complete one-sided group tester and headline wrapper
-- statement:
--   The core tester verifies the identity, reconstructs the action, and runs at most three fresh preprocessing attempts, stopping at the first success. Three failures cause acceptance. On success it compares the original table with the stored evaluator at independent uniform ordered pairs and rejects at the first mismatch.
--
--   $$\bar\epsilon=\max\{\epsilon,n^{-2}\},\qquad q=\lceil5/\bar\epsilon\rceil.$$
--
--   The real accuracy is supplied through this table-independent integer budget in one charged conversion. The headline wrapper checks $n\le3$ exactly after loading all table entries. For $\epsilon\ge1/2$ it uses the $1/4$ core branch. All later computations use finite words, with no free group enumeration or assumed-correct evaluator. Perfect completeness and far-input soundness are predicates on this fixed program, not properties stored inside it.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 2, 22–24, Theorem 1.1 and §§3.3–3.5

import Definitions.Def_FiniteGroupTesting_LinearQuery_FastEvaluation

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

noncomputable def accuracyBudget (n : ℕ) (ε : ℝ) : ℕ :=
  ⌈5 / max ε ((n : ℝ)⁻¹ ^ 2)⌉₊

/-- Only iid ordered-pair queries access the original table after preprocessing. -/
def comparePairs {n : ℕ} (e : Fin n) (ev : FastEvaluator n) : ℕ → OracleRun n Bool
  | 0 => pure true
  | q + 1 => do
      charge 6
      let i ← draw (n - 1)
      let j ← draw (n - 1)
      let x := labelAt e i.val
      let y := labelAt e j.val
      let expected ← evaluate ev x y
      let actual ← ask x y
      if expected != actual then return false
      comparePairs e ev q

def preprocessingRetries {n : ℕ} (A B : ℕ) (a : StoredAction n)
    (e : Fin n) (q : ℕ) : ℕ → OracleRun n Bool
  | 0 => pure true
  | attempts + 1 => do
      let result ← preprocessing A B a e
      match result with
      | none => preprocessingRetries A B a e q attempts
      | some ev => comparePairs e ev q

/-- Section 3.5: three attempts; all failures accept, never reject a true group for bad luck. -/
def coreTester {n : ℕ} (A B q : ℕ) (first : Fin n) : OracleRun n Bool := do
  let identity ← identityProgram first
  match identity with
  | none => return false
  | some e =>
      let reconstructed ← reconstruction e
      match reconstructed with
      | none => return false
      | some a => preprocessingRetries A B a e q 3

def loadTable {n : ℕ} (first : Fin n) :
    ℕ → Table n → OracleRun n (Table n)
  | 0, stored => pure stored
  | fuel + 1, stored => do
      charge 8
      let index := n * n - (fuel + 1)
      let x := labelAt first (index / n)
      let y := labelAt first (index % n)
      let z ← ask x y
      loadTable first fuel (Function.update stored x (Function.update (stored x) y z))

/-- Bounded-size exact check, using only the already loaded table.
The explicit loops are over labels, identities, and two-sided inverse candidates. -/
def exactGroupBoolean {n : ℕ} (first : Fin n) (stored : Table n) : Bool :=
  let xs := (List.range n).map (labelAt first)
  (xs.all fun x => xs.all fun y => xs.all fun z => stored (stored x y) z == stored x (stored y z)) &&
  (xs.any fun e =>
    (xs.all fun x => stored e x == x && stored x e == x) &&
    (xs.all fun x => xs.any fun y => stored x y == e && stored y x == e))

def exactSmallTester {n : ℕ} (first : Fin n) : OracleRun n Bool := do
  let stored ← loadTable first (n * n) (fun _ _ => first)
  charge (100 * (n + 1) ^ 4)
  return exactGroupBoolean first stored

/-- One fixed program family. The real accuracy is presented as its table-independent integer
budget in one charged input conversion; all subsequent work uses finite-word instructions. -/
noncomputable def headlineTester (A B n : ℕ) (ε : ℝ) : OracleRun n Bool :=
  if hn : 0 < n then
    let first : Fin n := ⟨0, hn⟩
    if n < 4 then exactSmallTester first
    else .step 1 (coreTester A B (accuracyBudget n (if ε < 1/2 then ε else 1/4)) first)
  else pure true

/-- Section 3.5 on its section's full domain; the initial conversion is charged. -/
noncomputable def sectionTester (A B n : ℕ) (ε : ℝ) : OracleRun n Bool :=
  if hn : 0 < n then .step 1 (coreTester A B (accuracyBudget n ε) ⟨0, hn⟩)
  else pure true

/-- Perfect completeness and the conventional 2/3 far-input rejection guarantee. -/
def TestsGroups {n : ℕ} (ε : ℝ) (p : OracleRun n Bool) : Prop :=
  (∀ op : Table n, IsGroupLaw op → probability op (· = true) p = 1) ∧
  (∀ op : Table n, Far ε op → (2/3 : ℝ) ≤ probability op (· = false) p)

end FiniteGroupTesting.LinearQuery


