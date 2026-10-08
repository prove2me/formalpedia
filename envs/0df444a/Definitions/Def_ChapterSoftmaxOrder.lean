-- Prove2me | Definitions.Def_ChapterSoftmaxOrder
-- name    : ChapterSoftmaxOrder
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T14:51:49.89043+00:00
-- url     : https://prove2.me/theorems/c8dbc2be-b53d-4261-8450-15025094a1f8
-- title:
--   Chapter SoftmaxOrder
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSoftmaxOrder.lean`): generated def bundle for ChapterSoftmaxOrder. See BookProof/ChapterSoftmaxOrder.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSoftmaxOrder.lean

import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib

/-!
# Chapter "The Coherent State of Attention": the order structure of Softmax

`ChapterSoftmaxSharpness` describes the two *extremes* of the Softmax family — the
uniform distribution at infinite temperature and the winner-takes-all limit at zero
temperature.  In between, the chapter's reading of Softmax as a *measurement* rests
on two structural facts that this module proves.

* `scoreSoftmax_shift` — **gauge invariance.**  Adding a constant to every score
  leaves the distribution unchanged: only score *differences* are physical.  This
  is the abstract form of the cancellation of the query penalty `exp(-‖q‖²)` in
  `coherentBorn_cancel_q`.
* `scoreSoftmax_le_iff` / `scoreSoftmax_lt_iff` / `scoreSoftmax_inj_iff` — at any
  positive inverse temperature, Softmax is a strictly increasing reparametrization
  of the scores: it *reorders nothing*.  Hence `scoreSoftmax_argmax`: the maximizer
  of the scores is the maximizer of the attention weights, at every temperature.
* `scoreSoftmax_const` — a flat score profile gives the uniform distribution at
  every temperature, so sharpening requires genuine score contrast.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/
namespace BookProof.ChapterSoftmaxOrder

end BookProof.ChapterSoftmaxOrder


