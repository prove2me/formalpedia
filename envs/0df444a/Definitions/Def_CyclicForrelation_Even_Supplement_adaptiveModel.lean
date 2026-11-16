-- Prove2me | Definitions.Def_CyclicForrelation_Even_Supplement_adaptiveModel
-- name    : CyclicForrelation_Even_Supplement_adaptiveModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:46:10.90223+00:00
-- url     : https://prove2.me/theorems/ffdf07b0-5966-4203-b6d7-d05ca9ada0ce
-- title:
--   Private-randomness adaptive real-output oracle algorithms
-- statement:
--   Let $Q$ be a finite set of query locations and $f:Q\to\{-1,1\}$ an arbitrary oracle. A **randomized adaptive algorithm** has an arbitrary measurable private seed probability space, a next-query rule $\nu(s,a)\in Q\cup\{\mathrm{stop}\}$, and a real output rule $g(s,a)$. Here $s$ is the private seed and $a$ is the ordered Boolean answer list so far. Both rules are measurable in $s$ for each fixed $a$ and receive no oracle argument. Earlier query locations are reconstructible from the seed and preceding answers, so the answer history contains all information available to a decision tree. The rule may repeat queries and stop at different times on different runs. All output randomness is included in $s$.
--
--   Starting with $a_0=[]$, at each step append $f(\nu(s,a_i))$ when a location is requested; after stop, the list stays fixed. A finite execution horizon $h$ supplies a bounded-depth tree, and the real output is
--   $$\operatorname{out}_A(f,s)=g(s,a_h).$$
--   Its cost on a run is $|a_h|$, charging every actual query including repetitions. Cost at most $q$ means $|a_h(f,s)|\le q$ for every oracle $f$ and every seed $s$. For a target $T:(Q\to\{-1,1\})\to\mathbb R$, success to accuracy $\varepsilon$ with probability $p$ means a measurable success event on each fixed input and
--   $$\forall f,\qquad \Pr_s\{|\operatorname{out}_A(f,s)-T(f)|\le\varepsilon\}\ge p.$$
--
--   This general oracle interface supplies the adaptive model used by Theorem 16. Exhaustive evaluation asks every location once and applies $T$ to the reconstructed oracle; the structural reconstruction and feasibility proofs establish exact correctness with $|Q|$ queries, independently of any complexity bound.
--
--   **Formalization Note** False encodes $+1$ and true encodes $-1$. The finite horizon limits query execution, with no limit on free computation or seed information. Every strategy with worst-case query cost $q$ is represented by taking horizon $q$: stopping steps are inert and every nonstopping step makes one query. Conversely each represented run is a decision tree execution. Thus minimizing over this interface retains arbitrary bounded randomized adaptive strategies, including correlated randomness, early stopping, repeated queries and real randomized outputs.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 4, §1.1 and footnote 2 (adaptive randomized algorithms); pp. 21–22, §5

import Definitions.Def_CyclicForrelation_Even_queryModel

namespace CyclicForrelation.Even.Supplement

/-- A private-randomness adaptive Boolean-oracle algorithm on a query alphabet `Q`.
On seed `s`, after the answers `a` observed so far (in order), `nextQuery s a` is the next
location to query, or `none` to stop. Since earlier queries are determined by the seed and
earlier answers, this is a general randomized decision tree; repeated queries are allowed.
`output s a` is the real estimate after stopping with answers `a`. Neither field sees the
oracle. `fuel` is only the number of execution steps; the cost is counted separately. -/
structure AdaptiveAlgorithm (Q : Type) where
  Seed : Type
  seedMeasurable : MeasurableSpace Seed
  law : @MeasureTheory.Measure Seed seedMeasurable
  probability : @MeasureTheory.IsProbabilityMeasure Seed seedMeasurable law
  nextQuery : Seed → List Bool → Option Q
  nextQuery_measurable : ∀ a, @Measurable Seed (Option Q) seedMeasurable ⊤
    (fun s => nextQuery s a)
  output : Seed → List Bool → ℝ
  output_measurable : ∀ a, @Measurable Seed ℝ seedMeasurable inferInstance
    (fun s => output s a)
  fuel : ℕ

/-- One execution step: ask the next query and record its answer, or stay put after stopping. -/
def adaptiveStep {Q : Type} (A : AdaptiveAlgorithm Q) (f : Q → Bool) (s : A.Seed)
    (a : List Bool) : List Bool :=
  match A.nextQuery s a with
  | none => a
  | some x => a ++ [f x]

/-- The answer list after `i` execution steps on oracle `f` and seed `s`. -/
def adaptiveTranscript {Q : Type} (A : AdaptiveAlgorithm Q) (f : Q → Bool) (s : A.Seed)
    (i : ℕ) : List Bool :=
  (adaptiveStep A f s)^[i] []

/-- The estimate returned after the execution; it sees only the seed and the answers. -/
def adaptiveRun {Q : Type} (A : AdaptiveAlgorithm Q) (f : Q → Bool) (s : A.Seed) : ℝ :=
  A.output s (adaptiveTranscript A f s A.fuel)

/-- Number of queries actually made (one answer per query, repetitions charged). -/
def adaptiveQueryCount {Q : Type} (A : AdaptiveAlgorithm Q) (f : Q → Bool) (s : A.Seed) : ℕ :=
  (adaptiveTranscript A f s A.fuel).length

/-- Worst-case total cost: at most `q` queries on every input and every seed. -/
def AdaptiveCostAtMost {Q : Type} (A : AdaptiveAlgorithm Q) (q : ℕ) : Prop :=
  ∀ f s, adaptiveQueryCount A f s ≤ q

/-- Success on each fixed input, with a measurable success event. -/
def AdaptiveEstimates {Q : Type} (A : AdaptiveAlgorithm Q) (target : (Q → Bool) → ℝ)
    (ε p : ℝ) : Prop :=
  ∀ f, @MeasurableSet A.Seed A.seedMeasurable {s | |adaptiveRun A f s - target f| ≤ ε} ∧
    ENNReal.ofReal p ≤ A.law {s | |adaptiveRun A f s - target f| ≤ ε}

/-- Exhaustive evaluation as an adaptive algorithm: query every location once, in the fixed
enumeration order, then evaluate the target on the reconstructed oracle. -/
noncomputable def adaptiveExhaustive {Q : Type} [Fintype Q]
    (target : (Q → Bool) → ℝ) : AdaptiveAlgorithm Q where
  Seed := Unit
  seedMeasurable := inferInstance
  law := MeasureTheory.Measure.dirac ()
  probability := inferInstance
  nextQuery := fun _ a => (allQueries Q)[a.length]?
  nextQuery_measurable := fun _ => measurable_const
  output := fun _ a => target (decodeAnswers a)
  output_measurable := fun _ => measurable_const
  fuel := Fintype.card Q

theorem adaptiveExhaustive_transcript {Q : Type} [Fintype Q] (target : (Q → Bool) → ℝ)
    (f : Q → Bool) (s : Unit) (i : ℕ) :
    adaptiveTranscript (adaptiveExhaustive target) f s i = ((allQueries Q).take i).map f := by
  induction i with
  | zero => simp [adaptiveTranscript]
  | succ i ih =>
    have hstep : adaptiveTranscript (adaptiveExhaustive target) f s (i + 1) =
        adaptiveStep (adaptiveExhaustive target) f s
          (adaptiveTranscript (adaptiveExhaustive target) f s i) :=
      Function.iterate_succ_apply' _ _ _
    rw [hstep, ih]
    simp only [adaptiveStep, adaptiveExhaustive, List.length_map, List.length_take]
    by_cases hi : i < (allQueries Q).length
    · rw [min_eq_left hi.le, List.getElem?_eq_getElem hi, List.take_add_one,
        List.getElem?_eq_getElem hi]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
    · rw [not_lt] at hi
      rw [min_eq_right hi, List.getElem?_eq_none le_rfl, List.take_of_length_le hi,
        List.take_of_length_le (by omega)]

/-- Exhaustive evaluation is feasible: cost `card Q` and exact output on every input. -/
theorem adaptive_exhaustive_feasible {Q : Type} [Fintype Q] (target : (Q → Bool) → ℝ)
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : p ≤ 1) :
    AdaptiveCostAtMost (adaptiveExhaustive target) (Fintype.card Q) ∧
      AdaptiveEstimates (adaptiveExhaustive target) target ε p := by
  have hlen : (allQueries Q).length = Fintype.card Q := by simp [allQueries]
  have htr : ∀ f s, adaptiveTranscript (adaptiveExhaustive target) f s
      (adaptiveExhaustive target).fuel = (allQueries Q).map f := by
    intro f s
    refine (adaptiveExhaustive_transcript target f s _).trans ?_
    congr 1
    exact List.take_of_length_le (by simp [adaptiveExhaustive, hlen])
  constructor
  · intro f s
    simp [adaptiveQueryCount, htr, hlen]
  · intro f
    have he : {s | |adaptiveRun (adaptiveExhaustive target) f s - target f| ≤ ε} =
        (Set.univ : Set Unit) := by
      ext s
      simp only [adaptiveRun, htr]
      simp [adaptiveExhaustive, hε]
    constructor
    · rw [he]
      exact MeasurableSet.univ
    · rw [he]
      change ENNReal.ofReal p ≤
        (MeasureTheory.Measure.dirac () : MeasureTheory.Measure Unit) Set.univ
      simpa only [MeasureTheory.measure_univ, ENNReal.ofReal_one] using
        (ENNReal.ofReal_le_ofReal hp)

end CyclicForrelation.Even.Supplement


