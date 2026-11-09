-- Prove2me | Definitions.Def_CNFLearning873_Valiant_Execution
-- name    : CNFLearning873_Valiant_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:10:24.247204+00:00
-- url     : https://prove2.me/theorems/47353e7c-9e98-4ff4-9380-8878036c0a7c
-- title:
--   Costed enumeration and filtering implementation of Valiant’s algorithm
-- statement:
--   An execution enumerates increasing variable subsets, attaches every sign pattern, tests each candidate against the samples, and emits exactly the survivors as literal lists. The generator branches by including the first remaining variable with either sign or omitting it. It emits one empty list when the remaining requested width is zero.
--
--   $$\operatorname{run}(n,k,x_1,\ldots,x_N)=(\text{emitted clause lists},\ \text{primitive-operation count}).$$
--
--   The recursively accumulated counter charges enumeration calls, branches, list allocation and concatenation, sample and coordinate reads, sign tests, loop steps, sample-index construction, and output copying. Coordinate access is unit cost; bit complexity is not claimed. Decoding the emitted list as a mathematical clause set is a representation map rather than a duplicate-removal step in the execution. No bound is built into the counter.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Valiant’s algorithm and computational complexity convention, p.2; Theorem 4.1, p.12 (PDF pp.2,12)

import Definitions.Def_CNFLearning873_Valiant_Learner

namespace CNFLearning873.Valiant

abbrev LiteralList (n : ℕ) := List (Fin n × Bool)

/-- Costed enumeration: recurse on the variable list, either omit its head or include
it with each sign. The k=0 branch emits one empty clause; no tuple deduplication.
The counter charges calls, branches, cons cells, and concatenation traversal. -/
def enumerate {n : ℕ} : List (Fin n) → ℕ → List (LiteralList n) × ℕ
  | _, 0 => ([[]], 2)
  | [], _ + 1 => ([], 1)
  | v :: vs, j + 1 =>
      let a := enumerate vs j
      let b := enumerate vs (j + 1)
      let inc := a.1.flatMap fun c => [(v, true) :: c, (v, false) :: c]
      (inc ++ b.1, a.2 + b.2 + 10 * a.1.length + 3)

/-- Each literal costs a coordinate read, sign comparison, Boolean operation and
loop step. All literals are examined; this only removes optional early stopping. -/
def testClause {n : ℕ} (x : Assignment n) : LiteralList n → Bool × ℕ
  | [] => (false, 1)
  | (v, b) :: cs =>
      let tail := testClause x cs
      (decide (x v = b) || tail.1, tail.2 + 5)

/-- The sample loop reads only the supplied examples, charging each lookup and test. -/
def testSamples {n N : ℕ} (xs : Fin N → Assignment n) (c : LiteralList n) :
    List (Fin N) → Bool × ℕ
  | [] => (true, 1)
  | i :: is =>
      let a := testClause (xs i) c
      let b := testSamples xs c is
      (a.1 && b.1, a.2 + b.2 + 3)

def filterCandidates {n N : ℕ} (xs : Fin N → Assignment n) :
    List (LiteralList n) → List (LiteralList n) × ℕ
  | [] => ([], 1)
  | c :: cs =>
      let a := testSamples xs c (List.finRange N)
      let b := filterCandidates xs cs
      (if a.1 then c :: b.1 else b.1,
        a.2 + b.2 + N + 4 + (if a.1 then c.length + 1 else 0))

/-- An execution of the enumeration/filter algorithm, including initialization,
sample-index construction and output construction. Costs are unit-cost list/array
operations, not bit complexity. The unknown formula is not an input. -/
def run {n N : ℕ} (k : ℕ) (xs : Fin N → Assignment n) : List (LiteralList n) × ℕ :=
  let a := enumerate (List.finRange n) k
  let b := filterCandidates xs a.1
  (b.1, n + 1 + a.2 + b.2)

def decodeClause {n : ℕ} (c : LiteralList n) : Clause n := fun v => c.lookup v

/-- Mathematical decoding of the emitted clauses; not an additional computation
charged to run. The learner emits the literal lists themselves. -/
def decodedOutput {n N : ℕ} (k : ℕ) (xs : Fin N → Assignment n) : CNF n :=
  ((run k xs).1.map decodeClause).toFinset

end CNFLearning873.Valiant


