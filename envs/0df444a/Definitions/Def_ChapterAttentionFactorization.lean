-- Prove2me | Definitions.Def_ChapterAttentionFactorization
-- name    : ChapterAttentionFactorization
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:30:48.283104+00:00
-- url     : https://prove2.me/theorems/8d146707-67ea-4525-8dae-fe31965b2607
-- title:
--   Chapter AttentionFactorization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionFactorization.lean`): generated def bundle for ChapterAttentionFactorization. See BookProof/ChapterAttentionFactorization.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionFactorization.lean

import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention" — independent modes factorize

A multi-mode coherent state is a product state, and the alignment score of a
product key is the *sum* of the per-mode scores.  This module proves what that
does to the attention distribution: it factorizes, exactly.

Deliverables (all `sorry`-free, `axiom`-free):

* `prodSoftmax β s₁ s₂` — Softmax over the product key set `Fin m₁ × Fin m₂` with
  additive scores `s(a,b) = s₁(a) + s₂(b)`;
* **`prodSoftmax_eq_mul`** — the headline: `p(a,b) = p₁(a)·p₂(b)`, a product
  measure.  Independent modes never entangle the attention distribution;
* `prodSoftmax_sum_one`, `prodSoftmax_pos` — it is a probability distribution;
* `prodSoftmax_marginal_left` / `prodSoftmax_marginal_right` — its marginals are
  the single-mode attention distributions, so ignoring a mode costs nothing;
* `shannonEntropy_prodSoftmax` — **the attention entropy is additive over
  independent modes**, the informational counterpart of the factorization.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionFactorization

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterAttentionEntropy

variable {m₁ m₂ : ℕ}

/-! ## Attention over a product of modes -/

/-- Softmax over a product key set with **additive** alignment scores. -/
def prodSoftmax (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ) (j : Fin m₁ × Fin m₂) : ℝ :=
  Real.exp (beta * (s₁ j.1 + s₂ j.2)) /
    ∑ l : Fin m₁ × Fin m₂, Real.exp (beta * (s₁ l.1 + s₂ l.2))













/-! ## Additivity of the attention entropy -/

/-- Shannon entropy of a distribution over a product key set. -/
def shannonEntropyProd (p : Fin m₁ × Fin m₂ → ℝ) : ℝ :=
  -∑ j : Fin m₁ × Fin m₂, p j * Real.log (p j)



end BookProof.ChapterAttentionFactorization

end


