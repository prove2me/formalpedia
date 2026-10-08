-- Prove2me | Definitions.Def_ChapterAttentionRetrieval
-- name    : ChapterAttentionRetrieval
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:29:32.571267+00:00
-- url     : https://prove2.me/theorems/7f1f9bbd-46f4-43ca-9aad-b0b228ca3919
-- title:
--   Chapter AttentionRetrieval
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionRetrieval.lean`): generated def bundle for ChapterAttentionRetrieval. See BookProof/ChapterAttentionRetrieval.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionRetrieval.lean

import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterCoherentGeometry
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib

/-!
# Chapter "The Coherent State of Attention": quantitative retrieval

`ChapterSoftmaxSharpness` and `ChapterAttentionOutput` describe the
winner-takes-all behaviour of a head as a *limit* (`β → ∞`).  A memory that only
works in the limit is no memory at all, so this module replaces those limits by
explicit, non-asymptotic bounds at a fixed inverse temperature.

The single hypothesis is a **score margin**: the retrieved key `j` beats every
other key by at least `δ`.  Then

* `scoreSoftmax_le_exp_neg_margin` — every distractor carries weight at most
  `e^{-βδ}`;
* `one_sub_scoreSoftmax_le_of_margin` — the total weight leaking off the target is
  at most `(m-1)·e^{-βδ}`;
* `scoreSoftmax_ge_of_margin` — the target's own weight is at least
  `1/(1 + (m-1)e^{-βδ})`;
* `norm_headOutput_sub_le_of_margin` — **the head is an associative memory with
  exponentially small error**: the output differs from the stored value `v j` by
  at most `2C(m-1)e^{-βδ}`.

Two complements sharpen the picture.  `scoreSoftmax_ge_of_spread` is a *lower*
bound valid with no margin at all: at a finite temperature no key is ever
completely ignored (`p j ≥ e^{-βD}/m` for a score spread `D`), so attention is
never exactly sparse.  `bornWeight_ge_of_dist_margin` transports the retrieval
bound to the coherent-state picture of `ChapterCoherentGeometry`, where the margin
is a gap in *squared distance* between the query and the keys.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/
namespace BookProof.ChapterAttentionRetrieval

end BookProof.ChapterAttentionRetrieval


