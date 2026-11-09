-- Prove2me | Definitions.Def_CyclicForrelation_Even_queryModel
-- name    : CyclicForrelation_Even_queryModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:42.236217+00:00
-- url     : https://prove2.me/theorems/89c853ee-8499-47f1-a01e-8339ef81a0b0
-- title:
--   Private-randomness nonadaptive finite-oracle algorithms
-- statement:
--   Let $Q$ be a finite alphabet of oracle locations and let $f:Q\to\{-1,1\}$ be an arbitrary fixed oracle. A randomized nonadaptive algorithm consists of a probability space of private seeds, a measurable finite ordered query list $L(s)$ chosen from the seed alone, and a real-valued postprocessor $g(s,a)$ of the seed and ordered answer list. For each fixed answer list, the postprocessor is measurable. Its execution is
--   $$\operatorname{out}_A(f,s)=g\bigl(s,(f(x):x\in L(s))\bigr).$$
--   The predicate $\operatorname{CostAtMost}(A,q)$ requires $|L(s)|\le q$ for every seed, including outcomes of probability zero. Repeated locations are charged separately. For a target $T$, accuracy $\varepsilon$, and probability $p$, $\operatorname{Estimates}(A,T,\varepsilon,p)$ requires a measurable success event and
--   $$\forall f,\qquad\Pr_s\{|\operatorname{out}_A(f,s)-T(f)|\le\varepsilon\}\ge p.$$
--   This interface permits correlated queries, arbitrary measurable seed probability laws, variable query counts, and randomized postprocessing. All computation after querying is free; the postprocessor receives no oracle argument. The exhaustive algorithm enumerates all locations and reconstructs the oracle from its answer list. Its structural reconstruction and correctness lemmas establish feasibility for every nonnegative accuracy and $p\le1$.
--
--   **Formalization Note** Boolean values encode signs by false $=+1$ and true $=-1$. The query-list codomain has its full discrete sigma-algebra; the seed space and its probability law are arbitrary. Exhaustive enumeration uses an equivalence with a finite ordinal. A default Boolean value on malformed answer lists is never used by an actual exhaustive execution.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 4, §1.1 and footnote 2 (operational nonadaptive model)

import Mathlib

namespace CyclicForrelation.Even

/-- A private-randomness nonadaptive Boolean-oracle algorithm on a finite query alphabet.
The output has access only to the seed and the ordered answer list. -/
structure NonadaptiveAlgorithm (Q : Type) where
  Seed : Type
  seedMeasurable : MeasurableSpace Seed
  law : @MeasureTheory.Measure Seed seedMeasurable
  probability : @MeasureTheory.IsProbabilityMeasure Seed seedMeasurable law
  queries : Seed → List Q
  queries_measurable : @Measurable Seed (List Q) seedMeasurable ⊤ queries
  output : Seed → List Bool → ℝ
  output_measurable : ∀ a, @Measurable Seed ℝ seedMeasurable inferInstance
    (fun s => output s a)

/-- Answers are read only after the entire query list has been fixed. -/
def runAlgorithm {Q : Type} (A : NonadaptiveAlgorithm Q) (f : Q → Bool) (s : A.Seed) : ℝ :=
  A.output s ((A.queries s).map f)

/-- Every random outcome satisfies the total query bound; repeated queries are charged. -/
def CostAtMost {Q : Type} (A : NonadaptiveAlgorithm Q) (q : ℕ) : Prop :=
  ∀ s, (A.queries s).length ≤ q

/-- Success on each fixed input, with a measurable success event. -/
def Estimates {Q : Type} (A : NonadaptiveAlgorithm Q) (target : (Q → Bool) → ℝ)
    (ε p : ℝ) : Prop :=
  ∀ f, @MeasurableSet A.Seed A.seedMeasurable {s | |runAlgorithm A f s - target f| ≤ ε} ∧
    ENNReal.ofReal p ≤ A.law {s | |runAlgorithm A f s - target f| ≤ ε}

/-- Enumeration of a finite query alphabet, with no repeated location. -/
noncomputable def allQueries (Q : Type) [Fintype Q] : List Q :=
  List.ofFn (Fintype.equivFin Q).symm

/-- Reconstruct a Boolean oracle from the exhaustive answer list. The default is used
only for malformed lists; exhaustive execution always supplies the full list. -/
noncomputable def decodeAnswers {Q : Type} [Fintype Q] (a : List Bool) : Q → Bool :=
  fun x => a.getD ((Fintype.equivFin Q x).val) false

/-- Exhaustive evaluation is a genuine algorithm whose postprocessor uses only answers. -/
noncomputable def exhaustiveAlgorithm {Q : Type} [Fintype Q]
    (target : (Q → Bool) → ℝ) : NonadaptiveAlgorithm Q where
  Seed := Unit
  seedMeasurable := inferInstance
  law := MeasureTheory.Measure.dirac ()
  probability := inferInstance
  queries := fun _ => allQueries Q
  queries_measurable := measurable_const
  output := fun _ a => target (decodeAnswers a)
  output_measurable := fun _ => measurable_const

/-- Structural reconstruction identity for the exhaustive answer API. -/
@[simp] theorem decode_allQueries {Q : Type} [Fintype Q] (f : Q → Bool) :
    decodeAnswers ((allQueries Q).map f) = f := by
  classical
  funext x
  simp [decodeAnswers, allQueries, List.map_ofFn]

/-- Immediate cost and correctness API of exhaustive evaluation; this supplies the
nonempty set used by the later minimum, without assuming any complexity estimate. -/
theorem exhaustive_feasible {Q : Type} [Fintype Q] (target : (Q → Bool) → ℝ)
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : p ≤ 1) :
    CostAtMost (exhaustiveAlgorithm target) (Fintype.card Q) ∧
      Estimates (exhaustiveAlgorithm target) target ε p := by
  classical
  constructor
  · intro s
    simp [exhaustiveAlgorithm, allQueries]
  · intro f
    have he : {s | |runAlgorithm (exhaustiveAlgorithm target) f s - target f| ≤ ε} =
        (Set.univ : Set Unit) := by
      ext s
      simp [runAlgorithm, exhaustiveAlgorithm, hε]
    constructor
    · rw [he]
      exact MeasurableSet.univ
    · rw [he]
      change ENNReal.ofReal p ≤ (MeasureTheory.Measure.dirac () : MeasureTheory.Measure Unit) Set.univ
      simpa only [MeasureTheory.measure_univ, ENNReal.ofReal_one] using
        (ENNReal.ofReal_le_ofReal hp)

end CyclicForrelation.Even


