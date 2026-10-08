-- Prove2me | Definitions.Def_ChapterAttentionMixture
-- name    : ChapterAttentionMixture
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:45:42.362286+00:00
-- url     : https://prove2.me/theorems/e57583e7-2330-41d7-a642-d3deaf5f9257
-- title:
--   Chapter AttentionMixture
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionMixture.lean`): generated def bundle for ChapterAttentionMixture. See BookProof/ChapterAttentionMixture.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionMixture.lean

import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": many heads are one mixture

A transformer layer runs several attention heads in parallel and combines them.
Probabilistically, a bank of heads read by a common set of values is a **mixture**
of the individual attention distributions, and this module proves the three facts
that make the mixture picture work.

* `mixture_isProb` — a convex combination of attention distributions is again an
  attention distribution (a probability vector over the keys).
* `observableExpectation_mixture` — **the ensemble output is the weighted mean of
  the head outputs**: combining the heads' distributions first and reading the
  values once is the same as reading the values head by head and averaging.  This
  is why the "concatenate then project" construction of multi-head attention is
  legitimate.
* `le_shannonEntropy_mixture` — **mixing heads never destroys information.**  By
  concavity of `x ↦ -x log x`, the entropy of the mixture is at least the mean of
  the head entropies: a bank of confident but disagreeing heads produces an
  uncertain consensus, never the reverse.

The multi-head specializations `multiHead_output_eq_mean` and
`le_shannonEntropy_multiHead` apply all three to the Softmax heads of
`ChapterSoftmaxSharpness` — heads may differ both in their scores and in their
temperatures.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionMixture

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterObservableExpectation BookProof.ChapterAttentionOutput
  BookProof.ChapterAttentionEntropy

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The mixture of a bank of attention distributions -/

/-- The mixture of the distributions `p h` with mixing weights `w h`. -/
def mixture (w : Fin H → ℝ) (p : Fin H → Fin m → ℝ) (j : Fin m) : ℝ := ∑ h, w h * p h j







/-! ## The output of the ensemble -/



/-! ## Mixing heads never destroys information -/







/-! ## Multi-head attention -/

/-- The attention distribution of a bank of Softmax heads: head `h` has its own
scores `s h` and its own inverse temperature `beta h`. -/
def multiHead (w : Fin H → ℝ) (beta : Fin H → ℝ) (s : Fin H → Fin m → ℝ) :
    Fin m → ℝ :=
  mixture w (fun h => scoreSoftmax (beta h) (s h))







end BookProof.ChapterAttentionMixture

end


