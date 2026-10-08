-- Prove2me | Definitions.Def_ChapterCrossEntropyGradient
-- name    : ChapterCrossEntropyGradient
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T08:40:33.880032+00:00
-- url     : https://prove2.me/theorems/17e7a659-27a7-41f2-a601-8454d3f4158e
-- title:
--   Chapter CrossEntropyGradient
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCrossEntropyGradient.lean`): generated def bundle for ChapterCrossEntropyGradient. See BookProof/ChapterCrossEntropyGradient.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCrossEntropyGradient.lean

import Definitions.Def_ChapterSoftmaxJacobian
import Definitions.Def_ChapterLogPartitionConvex
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": the learning signal

If Softmax attention is the Born rule, then *training* an attention layer is
fitting a Born probability to an observed outcome.  The fitting criterion is the
negative log-likelihood of the observed key — the cross-entropy loss

`L(s) = log Z_β(s) − β·s_y = −log p_β(y)`,

the free energy minus the energy of the realized outcome.  This module proves the
three facts an optimizer relies on.

* `crossEntropyLoss_eq_neg_log`, `crossEntropyLoss_nonneg`,
  `crossEntropyLoss_eq_zero_iff` — the loss is the surprisal of the observed key:
  nonnegative, and zero exactly when the layer already puts all its weight there.
* `hasDerivAt_crossEntropyLoss_score` — **the gradient of the loss is `β·(p − y)`**:
  the classical backpropagation rule of a Softmax layer, here derived from the
  free-energy derivative `∂ log Z/∂sᵢ = β·pᵢ` of `ChapterSoftmaxJacobian`.  The
  update pushes the observed key up and every other key down, in proportion to the
  attention it currently receives.
* `crossEntropyGradient_sum_zero` — the gradient sums to zero over the keys: the
  update is a *transfer* of attention, tangent to the probability simplex, and so
  the gauge freedom `s ↦ s + c` of `ChapterSoftmaxOrder` is never excited.

Finally `convexOn_crossEntropyLoss` records that the loss is convex in the inverse
temperature (`log Z` is convex, `β·s_y` is linear), so temperature fitting is a
one-dimensional convex problem with no spurious minima.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterCrossEntropyGradient

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterSoftmaxFluctuation BookProof.ChapterSoftmaxJacobian
  BookProof.ChapterLogPartitionConvex

variable {m : ℕ}

/-! ## The loss -/

/-- The **cross-entropy loss** of a Softmax attention layer at the observed key
`y`: the free energy minus the energy of the observed outcome. -/
def crossEntropyLoss (beta : ℝ) (s : Fin m → ℝ) (y : Fin m) : ℝ :=
  logPartition beta s - beta * s y







/-! ## The gradient -/

/-- The gradient of the cross-entropy loss with respect to the score of the key
`i`: `β·(pᵢ − δᵢy)`. -/
def crossEntropyGradient (beta : ℝ) (s : Fin m → ℝ) (y i : Fin m) : ℝ :=
  beta * (scoreSoftmax beta s i - (if i = y then 1 else 0))











/-! ## Convexity in the temperature -/



end BookProof.ChapterCrossEntropyGradient

end


