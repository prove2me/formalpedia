-- Prove2me | Definitions.Def_ChapterAttentionCoarseGrain
-- name    : ChapterAttentionCoarseGrain
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:44:56.408117+00:00
-- url     : https://prove2.me/theorems/1f6ec758-4763-48f2-adc0-2eb197145a3d
-- title:
--   Chapter AttentionCoarseGrain
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionCoarseGrain.lean`): generated def bundle for ChapterAttentionCoarseGrain. See BookProof/ChapterAttentionCoarseGrain.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionCoarseGrain.lean

import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": coarse-graining the keys

A head does not really attend to *positions*; it attends to whatever the positions
stand for.  Duplicate a key, split a token in two, or group the context into
topics, and the Born measurement should not notice.  This module proves that it
does not: the correct bookkeeping is the **pushforward** of the attention
distribution along a grouping map `f : Fin m → Fin r`.

* `mergeWeights` — the coarse-grained distribution `P(y) = ∑_{f(x)=y} p(x)`, shown
  to be a probability distribution (`mergeWeights_nonneg`, `sum_mergeWeights`).
* `observableExpectation_merge` — **the headline**: if the values depend on the key
  only through its group, the output computed key-by-key and the output computed
  group-by-group agree; `headOutput_merge` states this for an attention head.
* `shannonEntropy_mergeWeights_le` — the **data-processing inequality** for the
  attention entropy: merging keys can only lose information, never create it.
* `mergeWeights_scoreSoftmax_of_fiber_const` — the multiplicity rule: if the scores
  depend only on the group, the coarse-grained weights are the Softmax of the group
  scores *weighted by the size of each group*.  Duplicating a key is not neutral —
  it doubles that key's share; only the values, not the weights, are invariant.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionCoarseGrain

open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
  BookProof.ChapterSoftmaxOrder BookProof.ChapterAttentionEntropy
  BookProof.ChapterAttentionOutput

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The pushforward of the attention distribution -/

/-- The **coarse-grained attention weights**: the total weight of each group. -/
def mergeWeights (f : Fin m → Fin r) (p : Fin m → ℝ) (y : Fin r) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x









/-! ## Coarse-graining does not move the output -/





/-! ## Data processing: coarse-graining destroys information -/





/-! ## Multiplicity: duplicated keys accumulate weight -/



end BookProof.ChapterAttentionCoarseGrain


