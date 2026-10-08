-- Prove2me | Definitions.Def_ChapterAttentionSink
-- name    : ChapterAttentionSink
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:34:14.775661+00:00
-- url     : https://prove2.me/theorems/0cc4942b-c693-429b-8c7f-b5c72cfc7c00
-- title:
--   Chapter AttentionSink
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionSink.lean`): generated def bundle for ChapterAttentionSink. See BookProof/ChapterAttentionSink.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionSink.lean

import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": the attention sink

Trained transformers reliably devote a large share of every head's attention to one
distinguished position — the beginning-of-sequence token — which carries no
information.  This "attention sink" is often described as a pathology; the algebra
of the Born measurement says it is a *gauge*: appending one extra key to a head
rescales all the original weights by one common factor and changes nothing else.

Writing `Fin.cons s₀ s : Fin (m+1) → ℝ` for the score family with the sink
prepended, and `w` for the weight the sink receives:

* `sinkWeight_pos`, `sinkWeight_lt_one` — the sink always takes a strictly positive
  share, never all of it.
* `scoreSoftmax_sink_succ` — **the headline**: every original key keeps exactly
  `(1 − w)` times the weight it had, so `sum_scoreSoftmax_sink_succ` gives the keys
  a total budget of `1 − w`.
* `scoreSoftmax_sink_odds` — the odds between two ordinary keys are untouched, and
  `scoreSoftmax_sink_lt` says each of them is strictly diluted.
* `headOutput_sink` — the output is the two-point average `w·v₀ + (1−w)·o` of the
  sink value and the sink-free output: a sink with value `0` simply shrinks the
  head's output by `1 − w`.
* `shannonEntropy_cons_scaled` and `shannonEntropy_sink` — the entropy chain rule
  for the sink: the head's entropy is the binary entropy of the sink share plus
  `(1 − w)` times the entropy of the ordinary keys.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionSink

open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
  BookProof.ChapterSoftmaxOrder BookProof.ChapterAttentionEntropy
  BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The score family with a sink prepended -/



/-- The weight the sink key receives. -/
def sinkWeight (beta s0 : ℝ) (s : Fin m → ℝ) : ℝ :=
  scoreSoftmax beta (Fin.cons s0 s) 0











/-! ## The sink rescales, it does not reorganize -/









/-! ## The output of a head with a sink -/



/-! ## The entropy chain rule for the sink -/





end BookProof.ChapterAttentionSink


