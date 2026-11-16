-- Prove2me | Definitions.Def_CNFLearning873_Valiant_Supplement_ThresholdFormula
-- name    : CNFLearning873_Valiant_Supplement_ThresholdFormula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:37:56.725743+00:00
-- url     : https://prove2.me/theorems/e7b36959-264a-4c0e-b120-81be9b683f2b
-- title:
--   Threshold CNF, count expansion and solution sampler
-- statement:
--   For a list $S$ of width-$k$ clauses, multiplicity is counted. Construct $H_S$ from the disjunctions of compatible clause subsets $J\subseteq\mathrm{supp}(S)$ satisfying $|J|<r+1$ and total multiplicity at least $r$. Duplicate literals are removed; incompatible forbidden assignments yield tautologies and are omitted. Thus the intended threshold is
--
--   $$\Omega(H_S)=\{x:\sum_{c\in S}\mathbf1[x\text{ violates }c]<r\}.$$
--
--   Counts enumerate the distinct cases whose total violated multiplicity is strictly less than $r$. A case query satisfies every remaining clause and negates each violated clause into its unit clauses, adding greedy clauses or a conditional assignment prefix. Duplicate query clauses are removed and contradictory units are detected before querying. A solution is sampled by conditional counts, one variable at a time, carrying the remaining total. The program accumulates every counting query and charges subset enumeration, query construction, and prefix updates. Subsets are enumerated by bounded cardinality, rather than constructing all subsets and then discarding the large ones.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Definition of H_S and Lemma 6.6, printed pp.27–29 = 1-based PDF pp.27–29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Supplement_OracleProgram

noncomputable section

namespace CNFLearning873.Valiant.Supplement
open scoped BigOperators
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Enumerates subsets up to size b, without traversing all subsets of larger size. -/
def smallSubsets {n : ℕ} (C : CNF n) (b : ℕ) : List (CNF n) :=
  ((List.range (min b C.card + 1)).flatMap fun j => C.toList.sublistsLen j).map List.toFinset

def multiplicity {n : ℕ} (S : List (Clause n)) (c : Clause n) : ℕ := S.count c

def subsetWeight {n : ℕ} (S : List (Clause n)) (J : CNF n) : ℕ :=
  ∑ c ∈ J, multiplicity S c

def compatible {n : ℕ} (J : CNF n) : Prop :=
  ∀ c ∈ J, ∀ d ∈ J, ∀ v b e, c v = some b → d v = some e → b = e

/-- Union of the literals of a compatible family, with duplicate literals removed. -/
def mergeClause {n : ℕ} (J : CNF n) : Clause n :=
  fun v => J.toList.findSome? fun c => c v

/-- The actual CNF H_S of p.27, not a predicate stipulating its intended solution set. -/
def thresholdFormula {n : ℕ} (r : ℝ) (S : List (Clause n)) : CNF n :=
  (((smallSubsets S.toFinset (Nat.ceil r)).filter fun J =>
    (J.card : ℝ) < r + 1 ∧ r ≤ (subsetWeight S J : ℝ) ∧ compatible J).map mergeClause).toFinset

/-- Unit clause requiring x_v=b. -/
def unitClause {n : ℕ} (v : Fin n) (b : Bool) : Clause n :=
  fun u => if u = v then some b else none

/-- Negating a clause gives a conjunction of unit clauses at the forbidden values. -/
def negatedClause {n : ℕ} (c : Clause n) : CNF n :=
  (support c).image fun v => unitClause v (!(c v).getD false)

def contradictoryUnits {n : ℕ} (F : CNF n) : Prop :=
  ∃ v : Fin n, unitClause v false ∈ F ∧ unitClause v true ∈ F

/-- Count cases have strict total multiplicity <r, unlike H_S construction's ≥r. -/
def countCases {n : ℕ} (r : ℝ) (S : List (Clause n)) : List (CNF n) :=
  (smallSubsets S.toFinset (Nat.ceil r)).filter fun J => (subsetWeight S J : ℝ) < r

/-- Extras are the greedy clauses and the conditional fixedUnits. Finsets deduplicate all clauses. -/
def caseQuery {n : ℕ} (S : List (Clause n)) (J extras : CNF n) : CNF n :=
  (S.toFinset \ J) ∪ J.biUnion negatedClause ∪ extras

/-- Every count expands to explicitly supplied width-at-most-k queries. Contradictory units
are detected without calling the oracle. No desired bound is part of this program. -/
def countThreshold {n : ℕ} (r : ℝ) (S : List (Clause n)) (extras : CNF n) : OProg n ℕ :=
  let cases := countCases r S
  let setup := (S.length + 1) ^ 2 * (n + 1) * (Nat.ceil r + 1) *
    ((smallSubsets S.toFinset (Nat.ceil r)).length + 1)
  .work setup (cases.foldl (fun p J => p.bind fun a =>
    let F := caseQuery S J extras
    let w := (n + 1) ^ 2 * (S.length + extras.card + 1) ^ 2
    .work w (if contradictoryUnits F then .ret a else .count F fun z => .ret (a + z)))
    (.ret 0))

/-- Chain-rule solution sampling, using one conditional count per variable. The current total
is carried forward; it is computed once before calling this program. -/
def sampleThresholdAux {n : ℕ} (r : ℝ) (S : List (Clause n)) :
    List (Fin n) → CNF n → Assignment n → ℕ → OProg n (Assignment n)
  | [], _, x, _ => .ret x
  | v :: vs, fixedUnits, x, total => do
      let z ← countThreshold r S (insert (unitClause v false) fixedUnits)
      let u ← OProg.draw total OProg.ret
      let b := decide (z ≤ u)
      OProg.work ((n + 1) ^ 2) <|
        sampleThresholdAux r S vs (insert (unitClause v b) fixedUnits)
          (Function.update x v b) (if b then total - z else z)

def sampleThreshold {n : ℕ} (r : ℝ) (S : List (Clause n)) (total : ℕ) :
    OProg n (Assignment n) :=
  sampleThresholdAux r S (List.finRange n) ∅ (fun _ => false) total

end CNFLearning873.Valiant.Supplement


