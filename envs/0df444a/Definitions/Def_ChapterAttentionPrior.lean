-- Prove2me | Definitions.Def_ChapterAttentionPrior
-- name    : ChapterAttentionPrior
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T01:47:03.118139+00:00
-- url     : https://prove2.me/theorems/b6fb6e2a-cd43-457a-b492-7b9bb1f7eccd
-- title:
--   Chapter AttentionPrior
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionPrior.lean`): generated def bundle for ChapterAttentionPrior. See BookProof/ChapterAttentionPrior.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionPrior.lean

import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": a logit bias is a prior

Real heads rarely score their keys on alignment alone: a learned per-key bias, a
relative-position bias, a repetition penalty or a class prior is added to the
logits before the Softmax.  Read through the Born rule, such a bias is not a hack —
it is the **prior** of the Bayesian update whose likelihood is `e^{β s}`.

Writing `w j > 0` for the prior weight of key `j`:

* `priorSoftmax` — the biased head `pⱼ ∝ wⱼ e^{β sⱼ}`, a probability distribution
  (`priorSoftmax_pos`, `priorSoftmax_sum_one`);
* **`priorSoftmax_eq_posterior`** — it *is* the Bayes posterior of
  `ChapterBayesInference` with prior `w` and likelihood `e^{β s}`;
* **`priorSoftmax_odds`** — the headline in odds form: posterior odds = prior odds
  × likelihood ratio, `pᵢ/pⱼ = (wᵢ/wⱼ)·e^{β(sᵢ−sⱼ)}`;
* `priorSoftmax_eq_scoreSoftmax_bias` — equivalently, the prior is exactly a score
  bias `sⱼ ↦ sⱼ + (log wⱼ)/β`: a logit bias and a prior are the same object;
* `priorSoftmax_smul` — only the *ratios* of the prior weights matter (its overall
  scale is a gauge), and `priorSoftmax_uniform` recovers plain Softmax;
* `priorSoftmax_zero` — at infinite temperature the head returns the normalized
  prior: with no evidence, the posterior is the prior.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionPrior

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterBayesInference

variable {m : ℕ}

/-! ## The biased head -/

/-- **Attention with a prior**: `pⱼ ∝ wⱼ·e^{β sⱼ}`. -/
def priorSoftmax (w : Fin m → ℝ) (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : ℝ :=
  w j * Real.exp (beta * s j) / ∑ l, w l * Real.exp (beta * s l)







/-! ## It is the Bayes posterior -/







/-! ## Gauge freedom and the two extremes -/







end BookProof.ChapterAttentionPrior

end


