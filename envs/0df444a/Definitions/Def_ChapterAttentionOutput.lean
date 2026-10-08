-- Prove2me | Definitions.Def_ChapterAttentionOutput
-- name    : ChapterAttentionOutput
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T01:31:24.629486+00:00
-- url     : https://prove2.me/theorems/63080b86-2729-4848-81c2-d14423e7c430
-- title:
--   Chapter AttentionOutput
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionOutput.lean`): generated def bundle for ChapterAttentionOutput. See BookProof/ChapterAttentionOutput.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionOutput.lean

import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib


/-!
# Chapter "The Coherent State of Attention" — the output as a function of the
temperature

`ChapterObservableExpectation` already identifies the attention output with the
expectation value `observableExpectation p v = ∑ⱼ pⱼ • vⱼ` of a contextual
observable, and proves that it lies in the convex hull of the values.  This
module studies the *temperature family* of that output: what the head returns as
the inverse temperature runs from `0` to `∞`, and how sensitive the answer is to
the weights.  Nothing here re-proves what that module already has; the
convex-hull and norm bounds are reused from it.

Deliverables (all `sorry`-free, `axiom`-free):

* `headOutput β s v` — the output of a Softmax head at inverse temperature `β`,
  defined as the expectation value of the values against `scoreSoftmax β s`;
* `headOutput_zero` — **at infinite temperature the head ignores the query** and
  returns the plain mean of the values;
* `tendsto_headOutput` — **winner-takes-all**: with a strict score maximizer the
  output converges to that single value vector as the temperature drops to zero.
  Together with the previous item, the temperature dial interpolates between the
  unconditional mean and a hard table lookup;
* `headOutput_mem_convexHull`, `norm_headOutput_le`, `headOutput_const` — the
  whole family stays inside the convex hull of the values (specializations of
  `ChapterObservableExpectation`);
* `norm_observableExpectation_sub_le` — the output is `ℓ¹`-stable in the weights,
  the vector-valued companion of `ChapterSoftmaxStability`;
* `attentionOutput_eq_headOutput` — under a common key norm the coherent-state
  Born output is the head output at inverse temperature `2`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

open Filter Topology

noncomputable section

namespace BookProof.ChapterAttentionOutput

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterSoftmaxBorn BookProof.ChapterObservableExpectation

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The output of a head at inverse temperature `β` -/

/-- The output of a Softmax head at inverse temperature `beta`: the expectation
value of the values against the attention distribution. -/
def headOutput (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : E :=
  observableExpectation (scoreSoftmax beta s) v











/-! ## The zero-temperature limit: a hard lookup -/



/-! ## Stability of the output -/



/-! ## The coherent-state head -/



end BookProof.ChapterAttentionOutput

end


