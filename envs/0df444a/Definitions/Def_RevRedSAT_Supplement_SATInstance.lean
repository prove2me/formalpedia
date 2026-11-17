-- Prove2me | Definitions.Def_RevRedSAT_Supplement_SATInstance
-- name    : RevRedSAT_Supplement_SATInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:58:08.908843+00:00
-- url     : https://prove2.me/theorems/44f66f6c-85dc-408e-9476-482e19bfad9f
-- title:
--   Min-Weight SAT, MaxSAT and MaxSAT Above Half instances
-- statement:
--   An instance is a CNF formula $\varphi$ on the variables $0,\dots,n-1$, given as a list of clauses, together with a number $k$, coded as the code of $\varphi$ followed by $k$ (App. C.5).
--
--   1. **Min-Weight SAT**: YES when some satisfying assignment sets at most $k$ variables to one.
--   2. **MaxSAT** with absolute target $K=k$: a solution is an assignment satisfying at least $K$ clause occurrences (its *score*). Repeated clauses count separately, a repeated literal does not, and an empty clause is never satisfied.
--   3. **MaxSAT Above Half** with excess $k$: every clause is nonempty, and a solution is an assignment satisfying at least $\lceil m/2\rceil+k$ of the $m$ clause occurrences.
--
--   **Formalization Note** $\lceil m/2\rceil$ is $(m+1)/2$ in natural-number division. A MaxSAT solution is given as the set $S$ of variables set to one (the assignment `assignOf S`), so that the published search notion `RevRedSAT.SearchWithin` returns it.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.5, pp.94–95

import Mathlib
import Definitions.Def_MainResults
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RevRedSAT_encCNF
import Definitions.Def_RevRedSAT_SearchWithin

set_option autoImplicit false

namespace RevRedSAT.Supplement

open RSListDecodingCapacity.AllRates

/-- **A CNF formula together with a number**: the instances of Min-Weight SAT (budget `k`), of
MaxSAT (absolute target `K`) and of MaxSAT Above Half (excess `k`).
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.5, pp.94–95.

**Formalization Note** The formula is a list of clauses on the variables `0, …, n − 1`
(`MainResults.CNF n`); for MaxSAT the list is the input multiset of clause occurrences. -/
structure SATInstance where
  /-- the number of variables -/
  n : ℕ
  /-- the formula (list of clauses) -/
  φ : MainResults.CNF n
  /-- the number: budget, target or excess -/
  k : ℕ

/-- The code of an instance: the code `encCNF` of the formula followed by the number in
self-delimiting binary. -/
def IsSATCode (I : SATInstance) (w : List Bool) : Prop :=
  w = encCNF I.φ ++ encNat I.k

/-- The number of variables an assignment sets to one. -/
def ones {n : ℕ} (a : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => a i = true).card

/-- **YES-instances of Min-Weight SAT** (App. C.5, p.94: "Given a CNF formula and a budget k, find a
satisfying assignment that sets at most k variables to one"). -/
def MinWeightYes (I : SATInstance) : Prop :=
  ∃ a : Fin I.n → Bool, SatBy a I.φ ∧ ones a ≤ I.k

/-- The **score** of an assignment (App. C.5, p.94: "the number of clause occurrences it satisfies";
repeated clauses count separately, repeating a literal does not increase a clause's contribution,
an empty clause is always false). -/
def score {n : ℕ} (a : Fin n → Bool) (φ : MainResults.CNF n) : ℕ :=
  φ.countP fun C => C.any fun l => a l.1 == l.2

/-- The assignment that sets exactly the variables of `S` to one. -/
def assignOf {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

/-- **Solutions of MaxSAT with an absolute target** `K = k` (App. C.5, p.94: "the question is
whether its score can be at least K"; §10, p.76: "We seek a truth assignment satisfying at least K
clauses, or determine that none exists"): a set `S` of variables such that the assignment setting
exactly the variables of `S` to one has score at least `K`.

**Formalization Note** An assignment is returned as the set of its variables set to one (every
assignment is `assignOf` of its set of ones), so the published search notion
`RevRedSAT.SearchWithin` applies; a YES-instance always has a solution supported on occurring
variables, so the returned set need not be longer than the input. -/
def MaxSATValid (I : SATInstance) (S : Finset (Fin I.n)) : Prop :=
  I.k ≤ score (assignOf S) I.φ

/-- **Solutions of MaxSAT Above Half** with excess `k` (App. C.5, p.95: "the target is
⌈m/2⌉ + k"), `m` the number of clause occurrences, `⌈m/2⌉ = (m + 1)/2` in `ℕ`: a set `S` of
variables whose assignment `assignOf S` has score at least `⌈m/2⌉ + k`. -/
def AboveHalfValid (I : SATInstance) (S : Finset (Fin I.n)) : Prop :=
  (I.φ.length + 1) / 2 + I.k ≤ score (assignOf S) I.φ

/-- The codes of MaxSAT Above Half instances (App. C.5, p.95: "Here all m input clause occurrences
are nonempty"): codes of instances whose clauses are all nonempty. -/
def IsAboveHalfCode (I : SATInstance) (w : List Bool) : Prop :=
  (∀ C ∈ I.φ, C ≠ []) ∧ IsSATCode I w

end RevRedSAT.Supplement


