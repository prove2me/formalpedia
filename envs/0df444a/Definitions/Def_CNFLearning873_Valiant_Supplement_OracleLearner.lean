-- Prove2me | Definitions.Def_CNFLearning873_Valiant_Supplement_OracleLearner
-- name    : CNFLearning873_Valiant_Supplement_OracleLearner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:39:06.623694+00:00
-- url     : https://prove2.me/theorems/7bd5f19f-f968-4ba2-a11c-4da30b12b691
-- title:
--   Three-step weighted-sampling and greedy oracle learner
-- statement:
--   The learner receives only the public parameters and its learning samples. Step 1 uses the published Valiant survivor family $C'$, returns True if it is empty, and otherwise initializes unit weights and stores True with count $2^n$. In each of $\ell$ rounds, Step 2 independently samples $100n\ell$ clauses with replacement proportional to their integer weights, counts the resulting $H_S$, stores a strict improvement, samples a solution of that round's candidate by conditional counts, and doubles violated-clause weights only when their total is at most $n^{2k}$. Step 3 repeatedly counts each possible surviving-clause conjunction and conjoins a first minimizer, for $\ell$ rounds. The output is
--
--   $$H_{S_{\rm best}}\wedge\bigwedge_{c\in G}c,$$
--
--   where an empty stored multiset denotes True. The code expands every count into the queries of Lemma 6.6 and materializes the final CNF; ordinary loop, query, sampling, and output-construction costs are charged explicitly. The ideal phase law is used for Lemmas 6.8–6.9. The implemented law uses bounded rejection and returns True on abort. Success averages over independent learning samples and internal randomness. No target, correct learner, success guarantee or cost bound is an input field.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), The algorithm, Steps 1–3; Lemmas 6.6–6.9, printed pp.27–30 = 1-based PDF pp.27–30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Supplement_ThresholdFormula
import Definitions.Def_CNFLearning873_Valiant_Supplement_OracleParameters
import Definitions.Def_CNFLearning873_Valiant_Supplement_LearningModel

noncomputable section

namespace CNFLearning873.Valiant.Supplement
open scoped BigOperators
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Canonical deterministic tie order is the order of the finite clause list. -/
def weightedSelect {n : ℕ} (w : Clause n → ℕ) : List (Clause n) → ℕ → Clause n
  | [], _ => fun _ => none
  | c :: cs, u => if u < w c then c else weightedSelect w cs (u - w c)

def drawClauses {n : ℕ} (C : CNF n) (w : Clause n → ℕ) :
    ℕ → OProg n (List (Clause n))
  | 0 => .ret []
  | M + 1 => do
      let u ← OProg.draw (∑ c ∈ C, w c) OProg.ret
      let c := weightedSelect w C.toList u
      let S ← drawClauses C w M
      OProg.work ((n + 1) * (C.card + 1) * (1 + (∑ c ∈ C, w c)).log2) (.ret (c :: S))

/-- Only data constructed by the algorithm, with no guarantees among the fields. -/
structure WeightedState (n : ℕ) where
  weights : Clause n → ℕ
  best : List (Clause n)
  bestCount : ℕ

def initialState (n : ℕ) : WeightedState n := ⟨fun _ => 1, [], 2 ^ n⟩

def weightedRound {n : ℕ} (k ℓ : ℕ) (C : CNF n) (st : WeightedState n) :
    OProg n (WeightedState n) := do
  let S ← drawClauses C st.weights (100 * n * ℓ)
  let z ← countThreshold (radius n) S ∅
  let best := if z < st.bestCount then S else st.best
  let bestCount := min z st.bestCount
  let x ← sampleThreshold (radius n) S z
  let total := ∑ c ∈ C, if Violates c x then st.weights c else 0
  let w := if total ≤ n ^ (2 * k) then
      (fun c => if c ∈ C ∧ Violates c x then 2 * st.weights c else st.weights c)
    else st.weights
  OProg.work ((n + 1) * (C.card + 1) * (2 + (∑ c ∈ C, st.weights c)).log2)
    (.ret ⟨w, best, bestCount⟩)

def weightedPhase {n : ℕ} (k ℓ : ℕ) (C : CNF n) :
    ℕ → WeightedState n → OProg n (WeightedState n)
  | 0, st => .ret st
  | j + 1, st => (weightedRound k ℓ C st).bind fun st' => weightedPhase k ℓ C j st'

/-- Materialize H_S only when returning a phase result or the final CNF. Intermediate counts
use the stored multiset, as on pp.28-29. -/
def phaseFormula {n : ℕ} (st : WeightedState n) : CNF n :=
  if st.best = [] then ∅ else thresholdFormula (radius n) st.best

/-- Step 1's empty-survivor branch precedes the weighted phase. -/
def phase2 {n T : ℕ} (k d : ℕ) (ε δ : ℝ) (xs : Fin T → Assignment n) :
    OProg n (WeightedState n) :=
  let C := output k xs
  let ℓ := rounds n k d ε δ
  if C = ∅ then .ret (initialState n) else weightedPhase k ℓ C ℓ (initialState n)

/-- Evaluate all greedy candidate counts and keep a first minimizer. -/
def greedyChoice {n : ℕ} (r : ℝ) (S : List (Clause n)) (G : CNF n) :
    List (Clause n) → Option (Clause n × ℕ) → OProg n (Option (Clause n × ℕ))
  | [], best => .ret best
  | c :: cs, best => do
      let z ← countThreshold r S (insert c G)
      let next := match best with
        | none => some (c, z)
        | some b => if z < b.2 then some (c, z) else best
      OProg.work (n + 1) (greedyChoice r S G cs next)

/-- Empty stored multiset denotes True, not H_empty. At r>0 the count expansion agrees. -/
def greedyPhase {n : ℕ} (C : CNF n) (S : List (Clause n)) : ℕ → CNF n → OProg n (CNF n)
  | 0, G => .ret G
  | j + 1, G => do
      let best ← greedyChoice (radius n) S G C.toList none
      match best with
      | none => .ret G
      | some b => OProg.work (n + 1) (greedyPhase C S j (insert b.1 G))

/-- The actual three-step learner: survivor filter, weighted phase, greedy phase, explicit CNF
materialization. The target formula is never supplied to this program. -/
def oracleLearner {n T : ℕ} (k d : ℕ) (ε δ : ℝ) (xs : Fin T → Assignment n) :
    OProg n (CNF n) :=
  let C := output k xs
  let ℓ := rounds n k d ε δ
  OProg.work ((n + 1) * (k + 1) * (T + 1) * ((candidates n k).card + 1)) <|
    if C = ∅ then .ret ∅ else do
      let st ← weightedPhase k ℓ C ℓ (initialState n)
      let G ← greedyPhase C st.best ℓ ∅
      let enum := smallSubsets st.best.toFinset (Nat.ceil (radius n))
      let construction := (n + 1) * (st.best.length + 1) ^ 2 *
        (Nat.ceil (radius n) + 1) * (enum.length + 1) + (n + 1) * (G.card + 1)
      OProg.work construction (.ret (phaseFormula st ∪ G))

/-- True is returned on rejection abort. No aborted output is described as uniform. -/
def returnedFormula {n : ℕ} (z : Report n (CNF n)) : CNF n := z.result.getD ∅

/-- Success integrates the independent product sample law with the implemented internal law. -/
def oracleSuccess {n : ℕ} (F : CNF n) (h : (solutions F).Nonempty)
    (k d : ℕ) (ε δ : ℝ) : ℝ :=
  let T := learningSamples n k d ε δ
  let L := rejectionLimit n (rounds n k d ε δ) δ
  ∑ xs : Fin T → Assignment n, (sampleLaw F h T).prob xs *
    probability (implemented L (oracleLearner k d ε δ xs))
      (fun z => GoodOutput F h ε (returnedFormula z))

end CNFLearning873.Valiant.Supplement


