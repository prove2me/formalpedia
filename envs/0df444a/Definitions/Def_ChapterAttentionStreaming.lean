-- Prove2me | Definitions.Def_ChapterAttentionStreaming
-- name    : ChapterAttentionStreaming
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:37:54.188868+00:00
-- url     : https://prove2.me/theorems/1464b6be-7748-4a35-87a3-86ed5ddde636
-- title:
--   Chapter AttentionStreaming
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionStreaming.lean`): generated def bundle for ChapterAttentionStreaming. See BookProof/ChapterAttentionStreaming.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionStreaming.lean

import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": decoding is an incremental update

A transformer generating text does not recompute its heads from scratch at every
step: it keeps the keys and values of the tokens it has already seen (the *KV
cache*) and appends one new pair per step.  This module proves that the cached
computation is exact, and identifies the update rule.

Writing `Fin.snoc s sₙ` for the score family with one new key appended and `w` for
the weight the new key receives:

* `newWeight_pos`, `newWeight_lt_one` — the fresh token always takes a strictly
  positive share, never all of it;
* `scoreSoftmax_snoc_castSucc` — every cached key keeps exactly `(1 − w)` times the
  weight it had, so the cached scores never need to be revisited;
* **`headOutput_snoc`** — the headline: the new output is the convex interpolation
  `(1 − w)·o_old + w·v_new` of the cached output and the new value, so a decoder can
  carry one vector forward instead of the whole context;
* `norm_headOutput_snoc_sub_le` — hence a fresh token moves the output by at most
  `w·‖v_new − o_old‖`: late tokens perturb an established summary only in
  proportion to the attention they win;
* `scoreSoftmax_snoc_odds` — appending a token leaves all the odds among the cached
  keys untouched.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionStreaming

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterObservableExpectation BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Appending one key -/





/-- The weight the freshly appended key receives. -/
def newWeight (beta sn : ℝ) (s : Fin m → ℝ) : ℝ :=
  scoreSoftmax beta (Fin.snoc s sn) (Fin.last m)









/-! ## The cache stays valid -/







/-! ## The decoding update rule -/





end BookProof.ChapterAttentionStreaming

end


