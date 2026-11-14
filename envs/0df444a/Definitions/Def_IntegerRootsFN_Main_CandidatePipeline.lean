-- Prove2me | Definitions.Def_IntegerRootsFN_Main_CandidatePipeline
-- name    : IntegerRootsFN_Main_CandidatePipeline
-- status  : Definition
-- author  : @fffmath
-- created : 2026-11-13T07:32:51.22573+00:00
-- url     : https://prove2.me/theorems/476cf317-11e8-4485-9adc-e5838144f464
-- title:
--   Uniform candidate-generation and source-routine interfaces
-- statement:
--   For positive degree and coefficient-bit parameters $n,b$, a candidate algorithm outputs a finite list containing every integer root, while allowing nonroots and duplicate entries. One finite multitape machine and fixed constants are required uniformly for all valid inputs. The list has at most $K_{\rm card}n$ entries, total evaluation-point size at most $K_{\rm size}b$, and actual running time bounded by a specified scale $F(n,b)$ times fixed powers of the shifted logarithms of $n+1$ and $b+1$.
--
--   The remaining predicates are interfaces for the exact assertions of Proposition A.3, Proposition 3.4, Lemma 3.5, and Lemma 2.2 already present in this mission. They only name propositions; this definition file asserts none of those propositions and supplies no algorithm or proof.
--
--   **Formalization Note.** The candidate contract retains literal finite-machine execution on the mission's signed binary words. It is an intermediate specification for candidate generation, before exact root filtering.
-- source:
--   https://github.com/fffmath/IntegerRootFinding/blob/530114e43024123e59ef91398e3cf8cda076556a/IntegerRootFinding/Algorithm/Candidates.lean#L449-L475 (candidate contract); https://github.com/fffmath/IntegerRootFinding/blob/530114e43024123e59ef91398e3cf8cda076556a/IntegerRootFinding/WithoutPan.lean#L26-L37 and #L61-L91 (elementary candidate assembly); source manuscript Theorem 1.1, Lemmas 2.2 and 3.5, Proposition 3.4 and Proposition A.3, as already formalized by this mission. The literal finite-machine interface is a compilation refinement of the repository Costed model, not a theorem imported from that repository.

import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ElementarySearch
import Definitions.Def_IntegerRootsFN_Main_ApproximationConstruction

set_option autoImplicit false

namespace IntegerRootsFN.Main

/-- An unfiltered candidate generator with uniform count, total size, and actual runtime. -/
def CandidateAlgorithm (F : ℕ → ℕ → ℝ) : Prop :=
  ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, ∃ k l Kcard Ksize : ℕ,
    0 < C ∧ ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      ∃ cs : List ℤ,
        (∀ r : ℤ, f.IsRoot r → r ∈ cs) ∧
        cs.length ≤ Kcard * n ∧
        pointSize cs ≤ Ksize * b ∧
        Runs M (polynomialWord f n b) (integersWord cs)
          (softBound C k l n b (F n b))

/-- Exact source-result interface, with no theorem asserted here. -/
def ElementarySearchContract : Prop :=
  ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
        (∀ r : ℤ, f.IsRoot r → 2 ≤ |r| → r ∈ searchCandidates f n b) ∧
        (searchCandidates f n b).length ≤ 21 * min n b ∧
        (pointSize (searchCandidates f n b) : ℝ) ≤
          21 * (5 * (min n b : ℕ) + (b : ℝ) + (1 : ℝ) / 2 * logTwo ((min n b : ℕ) + 1)) ∧
        Runs M (polynomialWord (truncate f n b) (min n b) b)
          (integersWord (searchCandidates f n b))
          (softBound C k l (min n b) b ((min n b : ℕ) ^ 3 * (b : ℝ) ^ 2))

/-- Exact source-result interface, with no theorem asserted here. -/
def ApproximationRoutineContract : Prop :=
  ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (d b : ℕ) (g : Polynomial ℤ), Valid g d b →
      ∃ (samples : Fin (d + 1) → ApproxGKR.GaussDyadic) (q : ℤ × ℤ)
        (B : ℕ) (ws : Fin d → ℤ × ℤ) (β : Fin d → GaussianRational),
        ApproximationTrace g d b samples q B ws β ∧
        (B : ℝ) ≤ C * approximationPrecision d b ∧
        CoversRoots (complexify g) (fun i => (β i).value) ∧
        logRootSize (fun i => (β i).value) ≤ rootSizeBound d b ∧
        (∑ i, ((β i).bitSize : ℝ)) ≤ softBound C k l d b ((d : ℝ) * (b + (d : ℝ))) ∧
        Runs M (polynomialWord g d b) (approximationOutputWord samples q B ws β)
          (softBound C k l d b ((d : ℝ) * (b + (d : ℝ))))

/-- Exact source-result interface, with no theorem asserted here. -/
def MultipointEvaluationContract : Prop :=
  ∀ K : ℕ, ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      ∀ cs : List ℤ, cs.length ≤ K * n →
        Runs M (evaluationWord f n b cs) (integersWord (cs.map f.eval))
          (softBound C k l n b ((n : ℝ) * b + n * (pointSize cs : ℝ)))

/-- Exact source-result interface, with no theorem asserted here. -/
def TruncationRootContract : Prop :=
  ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      min n b < n → ∀ r : ℤ, f.IsRoot r → 2 ≤ |r| →
      ∃ α : ℂ, (complexify (truncate f n b)).IsRoot α ∧ ‖(r : ℂ) - α‖ < 2

end IntegerRootsFN.Main


