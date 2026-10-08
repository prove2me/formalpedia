-- Prove2me | Definitions.Def_ChapterAttentionTopK
-- name    : ChapterAttentionTopK
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T08:38:42.163984+00:00
-- url     : https://prove2.me/theorems/a680293d-09fd-4ae0-a1a2-10da7b0d80a6
-- title:
--   Chapter AttentionTopK
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionTopK.lean`): generated def bundle for ChapterAttentionTopK. See BookProof/ChapterAttentionTopK.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionTopK.lean

import Definitions.Def_ChapterAttentionSparse
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": top-`k` is the optimal shortlist

`ChapterAttentionSparse` prices a shortlist `S` exactly: the sparse head differs
from the dense head by `2(1 − P(S))` in `ℓ¹`, where `P(S)` is the attention mass of
`S`.  The natural next question is which shortlist of a given size to pick.  The
answer is the obvious one, and this module proves it: the keys of largest weight.

* `sum_le_sum_of_isTop` — a general fact about non-negative weights: a set whose
  members all dominate every outsider carries at least as much mass as any set of
  the same size or smaller;
* **`attendedMass_le_of_isTop`** — hence the top-`k` shortlist maximizes the
  attended mass, and `l1dist_maskedSoftmax_le_of_isTop` — it therefore *minimizes*
  the `ℓ¹` error and (`norm_headOutput_topk_sub_le_of_isTop`) the output error among
  all shortlists of at most its size;
* `isTopWeight_of_isTopScore` — and at a positive temperature "the `k` largest
  weights" is the same shortlist as "the `k` largest scores", so the selection can
  be made before the Softmax is evaluated.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionTopK

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterAttentionMasking BookProof.ChapterAttentionMarkov
  BookProof.ChapterObservableExpectation BookProof.ChapterAttentionOutput
  BookProof.ChapterAttentionSparse

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Choosing the heaviest keys -/

/-- `S` collects the heaviest keys for the weights `p`: every member dominates every
outsider. -/
def IsTop (p : Fin m → ℝ) (S : Finset (Fin m)) : Prop :=
  ∀ x ∈ S, ∀ y ∉ S, p y ≤ p x



/-! ## Top-`k` attention -/









end BookProof.ChapterAttentionTopK

end


