-- Prove2me | Definitions.Def_ChapterSoftmaxDivergence
-- name    : ChapterSoftmaxDivergence
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T05:35:04.204621+00:00
-- url     : https://prove2.me/theorems/469b764b-4c5c-4484-ac26-82e429cce9e9
-- title:
--   Chapter SoftmaxDivergence
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSoftmaxDivergence.lean`): generated def bundle for ChapterSoftmaxDivergence. See BookProof/ChapterSoftmaxDivergence.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSoftmaxDivergence.lean

import Definitions.Def_ChapterSoftmaxMaxEntropy
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention" — the divergence between two attention
distributions

`ChapterSoftmaxMaxEntropy` proves Gibbs' inequality in the entropy/cross-entropy
form.  This module packages the same content as a **relative entropy**
(Kullback–Leibler divergence) and computes it explicitly for two attention
distributions built from the *same* alignment scores at two different inverse
temperatures.

* `klDiv p q = ∑ⱼ pⱼ log (pⱼ / qⱼ)`, `klDiv_eq_crossEntropy_sub_shannonEntropy`;
* `klDiv_nonneg` — Gibbs' inequality; `klDiv_self` — a distribution is at zero
  divergence from itself;
* `klDiv_scoreSoftmax` — **the headline**: the divergence between the attention
  distributions at inverse temperatures `β` and `γ` is the *Bregman divergence of
  the log-partition function*,
  `KL(p_β ‖ p_γ) = log Z(γ) − log Z(β) − (γ − β)·⟨s⟩_β`;
* `logPartition_tangent_le` — consequently `log Z` lies above each of its tangent
  lines, the analytic shadow of the nonnegativity of the divergence;
* `fisherInformation` and `fisherInformation_eq_varScore` — the Fisher information
  of the attention family in the inverse temperature is exactly the score
  variance, i.e. the fluctuation of `ChapterSoftmaxFluctuation`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterSoftmaxDivergence

open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
  BookProof.ChapterSoftmaxOrder BookProof.ChapterSoftmaxFluctuation
  BookProof.ChapterSoftmaxMaxEntropy

variable {m : ℕ}

/-! ## The Kullback–Leibler divergence -/

/-- The **Kullback–Leibler divergence** (relative entropy) of `p` from `q`. -/
def klDiv (p q : Fin m → ℝ) : ℝ := ∑ j, p j * Real.log (p j / q j)





/-- A distribution is at zero divergence from itself. -/
@[simp] theorem klDiv_self (p : Fin m → ℝ) : klDiv p p = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases eq_or_ne (p j) 0 with h | h
  · simp [h]
  · rw [div_self h]; simp

/-! ## The divergence between two attention temperatures -/







/-! ## Fisher information -/

/-- The **Fisher information** of the attention family `β ↦ scoreSoftmax β s`,
`I(β) = ∑ⱼ pⱼ (∂_β log pⱼ)²`, written out with the Boltzmann score
`∂_β log pⱼ = sⱼ − ⟨s⟩_β`. -/
def fisherInformation (beta : ℝ) (s : Fin m → ℝ) : ℝ :=
  ∑ l, scoreSoftmax beta s l * (s l - meanScore beta s) ^ 2







end BookProof.ChapterSoftmaxDivergence

end


