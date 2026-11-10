-- Prove2me | Definitions.Def_CNFLearnMQ_learnCore
-- name    : CNFLearnMQ_learnCore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:22.331756+00:00
-- url     : https://prove2.me/theorems/e51325b8-df9e-4f6b-ae41-7d1547cf4d7f
-- title:
--   LearnCore$(X,\zeta)$ (Algorithm 1) as an oracle program
-- statement:
--   LearnCore recovers the core family $\mathcal R_X$ of a solution $X$ with membership queries. It keeps a list of discovered cores and a counter. Each **main-loop iteration**: builds a random candidate $R^*$ by including each variable independently with probability $p^\star=1/(16dk)$; **prunes** it by deleting, for each discovered core $R'\subseteq R^*$, one variable of $R'$ from $R^*$; **tests** $\Phi(X^{\oplus R^*})$. If the test is satisfied the counter grows. Otherwise the counter resets, $R^*$ is **shrunk** by repeatedly splitting it into $k+1$ nearly equal parts and removing a part whose removal keeps $\Phi(X^{\oplus R^*})=0$, until $|R^*|\le k$; then all subsets of $R^*$ are queried and a violating subset of minimum cardinality is added as a new core. The algorithm stops after $T$ consecutive unsuccessful iterations.
--
--   The module defines one main-loop iteration (`learnCoreIter`, used by Lemma 4.8), the loop, and LearnCore itself.
--
--   Charges per iteration: $1$ for the counter, $n$ coins and $n$ for building $R^*$, $|R'|+1$ per containment test and $1$ per deletion in pruning, a query (time $n$) for the test; $|R^*|+1$ plus a query per tried part when shrinking; $|R^*|+1$ plus a query per subset and $2^{|R^*|}(k+1)$ for the selection in the exhaustive search; $|R|+1$ to add a core; $1$ for computing $T$.
--
--   **Formalization Note** The paper's arbitrary choices are fixed: pruning deletes the smallest-index variable of $R'$; the parts are consecutive blocks of $R^*$ in increasing order, tried in order; the first minimum-cardinality violating subset in sublist order is chosen. A failed shrinking round or an empty exhaustive search (impossible under a genuine oracle and a solution, Lemma 4.6) stops shrinking or counts as an unsuccessful iteration, so the program terminates for every oracle; loop bounds (fuel) are never reached under a genuine oracle. LearnCore never receives $\Phi$.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Algorithm 1, p.18

import Mathlib
import Definitions.Def_CNFLearnMQ_OProg
import Definitions.Def_CNFLearnMQ_cores
import Definitions.Def_CNFLearnMQ_Ntot

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant OProg

variable {n : ℕ}

/-- Line 4 of Algorithm 1: include each listed variable independently with probability `p`
(one coin per variable). -/
def coinSubset (p : ℚ) : List (Fin n) → OProg n (Finset (Fin n))
  | [] => OProg.pure ∅
  | v :: vs => do
    let b ← bern p
    let S ← coinSubset p vs
    return (if b then insert v S else S)

/-- Lines 5–7 of Algorithm 1 (pruning): for each discovered core `R′`, in the order of discovery,
if `R′ ⊆ R*` then delete the smallest-index variable of `R′` from `R*`. Charge: `|R′| + 1` for each
containment test and `1` for each deletion (`R*` stored as a Boolean array). -/
def prune (found : List (Finset (Fin n))) (R : Finset (Fin n)) : OProg n (Finset (Fin n)) :=
  found.foldlM (fun R R' => do
    charge (R'.card + 1)
    if h : R' ⊆ R ∧ R'.Nonempty then do
      charge 1
      return R.erase (R'.min' h.2)
    else return R) R

/-- The sizes of `j` nearly equal parts of a set of size `m`: the first `m mod j` parts have size
`⌊m/j⌋ + 1`, the others `⌊m/j⌋`. -/
def blockSizes (m j : ℕ) : List ℕ :=
  (List.range j).map fun i => m / j + if i < m % j then 1 else 0

/-- Cut a list into consecutive pieces of the given lengths. -/
def chunks {α : Type} : List ℕ → List α → List (List α)
  | [], _ => []
  | s :: ss, l => l.take s :: chunks ss (l.drop s)

/-- Line 12 of Algorithm 1: the partition of `R` into `j` parts of nearly equal size, as
consecutive blocks of `R` in increasing variable order (sizes differ by at most one). -/
def blocks (j : ℕ) (R : Finset (Fin n)) : List (Finset (Fin n)) :=
  (chunks (blockSizes R.card j) (R.sort (· ≤ ·))).map List.toFinset

/-- Line 14 of Algorithm 1: query `Φ(X^{⊕(R*∖R*_i)})` for the parts in order until a non-satisfying
assignment is found; return `R* ∖ R*_i` for the first such `i` (or `none` if there is none, which
never happens under a genuine membership oracle and a solution `X`, Lemma 4.6). Charge `|R*| + 1`
per tried part for the set difference, plus the query. -/
def firstRemovable (X : Assignment n) (R : Finset (Fin n)) :
    List (Finset (Fin n)) → OProg n (Option (Finset (Fin n)))
  | [] => OProg.pure none
  | P :: Ps => do
    charge (R.card + 1)
    let b ← ask (flipOn X (R \ P))
    if b then firstRemovable X R Ps else return some (R \ P)

/-- Lines 11–15 of Algorithm 1 (shrinking): while `|R*| > k`, partition `R*` into `k + 1` nearly
equal parts and remove the first part whose removal keeps `Φ(X^{⊕R*}) = 0`. The fuel argument
bounds the number of rounds; with fuel `n` it is never exhausted (each round removes a nonempty
part). If no part is removable (impossible under a genuine oracle, Lemma 4.6) shrinking stops. -/
def shrink (k : ℕ) (X : Assignment n) : ℕ → Finset (Fin n) → OProg n (Finset (Fin n))
  | 0, R => OProg.pure R
  | fuel + 1, R =>
    if R.card ≤ k then OProg.pure R else do
      let r ← firstRemovable X R (blocks (k + 1) R)
      match r with
      | none => return R
      | some R' => shrink k X fuel R'

/-- Lines 16–17 of Algorithm 1: query `Φ(X^{⊕R°})` for every `R° ⊆ R*` (in the order of the
sublists of `R*` sorted increasingly) and return the first queried violating subset of minimum
cardinality, or `none` if no subset is violating (impossible under a genuine oracle when
`Φ(X^{⊕R*}) = 0`). Charge `|R*| + 1` per subset plus its query, and `2^{|R*|}(k + 1)` for the
selection. -/
def exhaustive (k : ℕ) (X : Assignment n) (R : Finset (Fin n)) :
    OProg n (Option (Finset (Fin n))) := do
  let subs := ((R.sort (· ≤ ·)).sublists).map List.toFinset
  let answers ← subs.mapM fun S => do
    charge (R.card + 1)
    let b ← ask (flipOn X S)
    return (S, b)
  charge (2 ^ R.card * (k + 1))
  return ((answers.filter fun p => !p.2).map Prod.fst).argmin Finset.card

/-- One main-loop iteration of LearnCore (Algorithm 1, lines 3–17, p.18) on the solution `X`, given
the list `found` of cores discovered so far. It returns `some R` when the testing query finds
`Φ(X^{⊕R*}) = 0` and the exhaustive search selects `R`, and `none` when the test is satisfied.
Charges: `1` for the iteration start and counter update; `n` coins plus `n` for building `R*`;
pruning, shrinking and exhaustive search as in their definitions.

**Formalization Note** The paper's arbitrary choices are fixed: the smallest-index variable is
deleted in pruning, the parts are consecutive blocks in increasing variable order and are tried in
order, and the first minimum-cardinality violating subset in sublist order is chosen. The program
never receives `Φ`; it learns about it only through membership queries. -/
def learnCoreIter (n k d : ℕ) (X : Assignment n) (found : List (Finset (Fin n))) :
    OProg n (Option (Finset (Fin n))) := do
  charge 1
  let R0 ← coinSubset (1 / (16 * (d : ℚ) * k)) (List.finRange n)
  charge n
  let R1 ← prune found R0
  let b ← ask (flipOn X R1)
  if b then return none
  else do
    let R2 ← shrink k X n R1
    exhaustive k X R2

/-- The main loop of LearnCore (Algorithm 1, lines 2–18): `T` is the stopping threshold, `cnt` the
number of consecutive unsuccessful iterations. A found core is added (charge `|R| + 1`) and resets
the counter. The fuel argument bounds the number of iterations; with fuel `(2^n + 1)·T` it is never
exhausted, because every added set is a new subset of the variables (proof of Lemma 4.7, p.18). An
iteration whose exhaustive search finds no violating subset (impossible under a genuine oracle)
counts as unsuccessful. -/
def learnCoreLoop (n k d : ℕ) (X : Assignment n) (T : ℕ) :
    ℕ → List (Finset (Fin n)) → ℕ → OProg n (List (Finset (Fin n)))
  | 0, found, _ => OProg.pure found
  | fuel + 1, found, cnt =>
    if T ≤ cnt then OProg.pure found else do
      let r ← learnCoreIter n k d X found
      match r with
      | none => learnCoreLoop n k d X T fuel found (cnt + 1)
      | some R => do
        charge (R.card + 1)
        learnCoreLoop n k d X T fuel (found ++ [R]) 0

/-- LearnCore(X, ζ) (Algorithm 1, p.18), with the parameters `n, d, k` and membership-query access
to `Φ`: it returns the family of discovered cores of the solution `X`. Charge `1` for computing `T`
(unit-cost real arithmetic). -/
noncomputable def learnCore (n k d : ℕ) (X : Assignment n) (ζ : ℝ) :
    OProg n (Finset (Finset (Fin n))) := do
  charge 1
  let T := coreRounds n k d ζ
  let found ← learnCoreLoop n k d X T ((2 ^ n + 1) * T) [] 0
  return found.toFinset

end CNFLearnMQ


