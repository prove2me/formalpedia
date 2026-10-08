-- Prove2me | Definitions.Def_ChapterSoftmaxJacobian
-- name    : ChapterSoftmaxJacobian
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T05:40:41.792446+00:00
-- url     : https://prove2.me/theorems/8439ee18-93f2-4f87-acb2-f81463ba0db7
-- title:
--   Chapter SoftmaxJacobian
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSoftmaxJacobian.lean`): generated def bundle for ChapterSoftmaxJacobian. See BookProof/ChapterSoftmaxJacobian.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSoftmaxJacobian.lean

import Definitions.Def_ChapterSoftmaxFluctuation
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention" — the score derivative of attention

`ChapterSoftmaxFluctuation` differentiates the attention distribution in the
*inverse temperature* `β`.  This module differentiates it in the *scores*
themselves: the alignment score `sᵢ` of a single key is nudged, and the response
of the free energy and of every attention weight is computed.  This is the
Jacobian that backpropagation through an attention head actually uses.

Deliverables (all `sorry`-free, `axiom`-free):

* `scorePerturb s i t` — the score profile `s` with `t` added to the `i`-th score
  only;
* `hasDerivAt_partition_score`, `hasDerivAt_logPartition_score` — **attention is
  the score gradient of the free energy**: `∂/∂sᵢ log Z = β·pᵢ`;
* `hasDerivAt_scoreSoftmax_score` — **the Jacobian of Softmax**:
  `∂pⱼ/∂sᵢ = β·pⱼ·(δᵢⱼ − pᵢ)`;
* `softmaxJacobian` and its structural laws: `softmaxJacobian_symm` (the Jacobian
  is symmetric, as a Hessian of `log Z` must be), `softmaxJacobian_row_sum_zero`
  (the total weight is conserved: a key can only gain what the others lose),
  `softmaxJacobian_diag_nonneg` / `softmaxJacobian_offDiag_nonpos` (raising a
  score helps that key and hurts every other one, at `β ≥ 0`);
* `softmaxJacobian_quadratic_form` — the quadratic form of the Jacobian is
  `β` times the attention-weighted variance of the test vector, hence
  `softmaxJacobian_posSemidef` at `β ≥ 0`;
* `softmaxJacobian_quadratic_form_score` — evaluated on the scores themselves it
  returns `β·Var_β(s)`, tying the score Jacobian to the fluctuation–response law
  of `ChapterSoftmaxFluctuation`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterSoftmaxJacobian

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

/-! ## Perturbing a single score -/

/-- The score profile `s` with `t` added to the score of the key `i` only. -/
def scorePerturb (s : Fin m → ℝ) (i : Fin m) (t : ℝ) : Fin m → ℝ :=
  fun l => s l + (if l = i then t else 0)

@[simp] theorem scorePerturb_zero (s : Fin m → ℝ) (i : Fin m) : scorePerturb s i 0 = s := by
  funext l
  simp [scorePerturb]





/-! ## Differentiating the partition function in a score -/









/-! ## The Jacobian of Softmax -/

/-- The **Softmax Jacobian** `∂pⱼ/∂sᵢ = β·pⱼ·(δᵢⱼ − pᵢ)`. -/
def softmaxJacobian (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) : ℝ :=
  beta * scoreSoftmax beta s j * ((if j = i then (1 : ℝ) else 0) - scoreSoftmax beta s i)





/-! ## Structure of the Jacobian -/









/-! ## The quadratic form: the Jacobian is a covariance -/

/-- The attention-weighted variance of an arbitrary test vector `x`. -/
def weightedVar (beta : ℝ) (s x : Fin m → ℝ) : ℝ :=
  (∑ j, scoreSoftmax beta s j * x j ^ 2) - (∑ j, scoreSoftmax beta s j * x j) ^ 2











end BookProof.ChapterSoftmaxJacobian

end


