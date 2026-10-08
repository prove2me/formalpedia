-- Prove2me | Definitions.Def_ChapterSoftmaxFluctuation
-- name    : ChapterSoftmaxFluctuation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:20:22.620035+00:00
-- url     : https://prove2.me/theorems/ff7c65f4-4a60-44f5-9410-db544f82f9a7
-- title:
--   Chapter SoftmaxFluctuation
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSoftmaxFluctuation.lean`): generated def bundle for ChapterSoftmaxFluctuation. See BookProof/ChapterSoftmaxFluctuation.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSoftmaxFluctuation.lean

import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention" — the fluctuation–response law of
attention

`ChapterAttentionEntropy` studies the attention distribution `scoreSoftmax β s`
at a *fixed* inverse temperature.  This module differentiates in `β`, and proves
the standard statistical-mechanics dictionary for the attention head:

* `partition` `Z(β) = ∑ⱼ exp (β sⱼ)` and `logPartition` `= log Z`;
* `hasDerivAt_logPartition` / `deriv_logPartition` — **the first response law**:
  `d/dβ log Z(β) = ⟨s⟩_β`, the attention-weighted mean score;
* `hasDerivAt_scoreSoftmax` — the response of a single attention weight,
  `d/dβ pⱼ(β) = pⱼ(β)·(sⱼ − ⟨s⟩_β)`: a key gains weight exactly when its score
  beats the current average;
* `hasDerivAt_meanScore` / `deriv_meanScore` — **the fluctuation–response law**:
  `d/dβ ⟨s⟩_β = Var_β(s) ≥ 0`.  Sharpening the attention (raising `β`, lowering the
  temperature) can only *increase* the mean score, and it does so at a rate equal
  to the variance of the scores under the current attention distribution;
* `varScore_eq_sub_sq` — `Var = ⟨s²⟩ − ⟨s⟩²`; `varScore_nonneg`;
* `varScore_eq_zero_iff`, `varScore_eq_zero_of_const`, `varScore_pos_of_ne` — the
  response vanishes exactly when every score already equals the mean, and is
  strictly positive as soon as two scores differ;
* `meanScore_monotone`, `meanScore_le_max` — the mean score is monotone in `β` and
  never exceeds the best score, so the response saturates.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterSoftmaxFluctuation

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

/-! ## The partition function -/

/-- The **partition function** of the attention head. -/
def partition (beta : ℝ) (s : Fin m → ℝ) : ℝ := ∑ l, Real.exp (beta * s l)

/-- The **log-partition (free energy) function**. -/
def logPartition (beta : ℝ) (s : Fin m → ℝ) : ℝ := Real.log (partition beta s)

/-- The **attention-weighted mean score** `⟨s⟩_β`. -/
def meanScore (beta : ℝ) (s : Fin m → ℝ) : ℝ := ∑ l, scoreSoftmax beta s l * s l

/-- The **attention-weighted variance of the scores** `Var_β(s)`. -/
def varScore (beta : ℝ) (s : Fin m → ℝ) : ℝ :=
  ∑ l, scoreSoftmax beta s l * (s l - meanScore beta s) ^ 2







/-! ## Differentiating the partition function -/









/-! ## Differentiating a single attention weight -/



/-! ## The fluctuation–response law -/













/-! ## The variance vanishes exactly on constant scores -/







end BookProof.ChapterSoftmaxFluctuation

end


