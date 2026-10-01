-- Prove2me | Definitions.Def_ChapterObservableExpectation
-- name    : ChapterObservableExpectation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T07:55:45.705813+00:00
-- url     : https://prove2.me/theorems/72c8890c-eebc-4699-bc2b-530ea6fda392
-- title:
--   Chapter ObservableExpectation
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterObservableExpectation.lean`): generated def bundle for ChapterObservableExpectation. See BookProof/ChapterObservableExpectation.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterObservableExpectation.lean

import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterBayesInference
import Mathlib


/-!
# Chapter "The Coherent State of Attention", §"The Posterior: Observable
Operators and Expectation Values"

Formalization of the third identity of the new chapter `Book/CoherentState.lean`:
the attention output

  `oᵢ = ∑ⱼ aᵢⱼ vⱼ`

is the **expectation value of a contextual observable** over the posterior
produced by the Born-rule measurement of the previous section.  By the spectral
theorem an observable is fixed by its eigenstates (the keys `|kⱼ⟩`) and its
eigenvalues (the values `vⱼ`), and its expectation value in a state whose Born
statistics are `pⱼ` is the probability-weighted sum `∑ⱼ pⱼ vⱼ`.

The mathematical core is finite and purely algebraic: it is the statement that
the attention output *is* a convex combination — an expectation — of the value
vectors, together with the fact that the weights produced in
`ChapterSoftmaxBorn` are a genuine probability distribution.

Deliverables (all `sorry`-free, `axiom`-free):

* `observableExpectation` — the probability-weighted sum `∑ⱼ pⱼ • vⱼ`;
* `observableExpectation_scalar` — for scalar eigenvalues it is the ordinary
  expectation `∑ⱼ pⱼ vⱼ`, matching `ChapterConditional` / `ChapterBayesInference`;
* `observableExpectation_const` — a sharp observable has its own value as
  expectation (normalization of the distribution);
* `observableExpectation_add`, `observableExpectation_smul` — linearity in the
  eigenvalues, the defining property of an expectation value;
* `prob_weighted_sum_mem_convexHull` — the expectation lies in the convex hull of
  the eigenvalues: measurement never leaves the span of the possible outcomes;
* `observableExpectation_norm_le` — and it is bounded by the largest eigenvalue
  norm;
* **HEADLINE `attention_eq_expectation`** — the Softmax/Born attention output is
  exactly the expectation value of the value-observable over the coherent-state
  Born posterior, and that posterior is a genuine probability distribution;
* `attention_mem_convexHull` — hence the attention output is a convex combination
  of the value vectors;
* `bayes_posterior_expectation_mem_convexHull` — the same packaging for the Bayes
  posterior of `ChapterBayesInference`, exhibiting the deep-learning layer as one
  complete Bayesian update.

**Recorded disparity with the informal chapter.**  The chapter writes the
observable as an operator `V̂ = ∑ⱼ vⱼ |kⱼ⟩⟨kⱼ|` and appeals to the spectral
theorem.  Here the observable is represented by its *spectral data* — the family
of eigenvalues `v : Fin m → E` indexed by the outcomes — and the theorem proved
is the expectation-value identity for that data.  Building the operator `V̂`
itself (and proving that the coherent states `|kⱼ⟩` are orthonormal, which they
are *not* — coherent states are overcomplete) is deliberately not attempted here;
the chapter's step is exactly the finite expectation identity formalized below.
**This disparity is now closed** by `BookProof.ChapterObservableOperator`, which
builds the operator `V̂ = ∑ⱼ vⱼ |kⱼ⟩⟨kⱼ|` as a matrix, proves it Hermitian for real
eigenvalues, and proves the operator expectation `⟨q|V̂|q⟩ = ∑ⱼ pⱼ vⱼ` with the Born
statistics `pⱼ = |⟨kⱼ|q⟩|²` (a probability distribution for an orthonormal
eigenbasis and a unit state).

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterObservableExpectation

open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ## The expectation value of an observable -/

/-- The **expectation value** of an observable with eigenvalues `v : Fin m → E`
in a state whose measurement statistics over the eigenbasis are `p : Fin m → ℝ`:
the probability-weighted sum `⟨V̂⟩ = ∑ⱼ pⱼ vⱼ`. -/
def observableExpectation (p : Fin m → ℝ) (v : Fin m → E) : E := ∑ j, p j • v j











/-! ## The expectation is a convex combination of the outcomes -/





/-! ## The attention output is an expectation value -/

/-- The **attention output** of a query against keys `k` with value vectors `v`:
the Born-weighted aggregation `oᵢ = ∑ⱼ aᵢⱼ vⱼ`. -/
def attentionOutput (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (v : Fin m → E) : E :=
  ∑ j, bornWeight q k j • v j







/-! ## The same packaging for the Bayes posterior -/

open BookProof.ChapterBayesInference

variable {Y : Type*}







end BookProof.ChapterObservableExpectation

end


