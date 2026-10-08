-- Prove2me | Definitions.Def_ChapterAttentionMarkov
-- name    : ChapterAttentionMarkov
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T05:38:35.353767+00:00
-- url     : https://prove2.me/theorems/b545c567-6e70-4cb8-8cba-e1b2ddfbe9ff
-- title:
--   Chapter AttentionMarkov
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionMarkov.lean`): generated def bundle for ChapterAttentionMarkov. See BookProof/ChapterAttentionMarkov.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionMarkov.lean

import Definitions.Def_ChapterAttentionRetrieval
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": attention is a Markov kernel

Read row-wise, an attention layer is a **stochastic matrix**: the row `i` is the
Born distribution of the query at position `i` over the keys.  Pushing a
distribution over positions through the layer is therefore a Markov step, and
stacking layers composes the kernels.  This module proves that the picture is
consistent and that it *contracts*.

* `attentionMatrix_isStochastic` — the rows are strictly positive and sum to one.
* `push_isProb`, `compose_isStochastic`, `push_compose` — pushing a probability
  vector through a layer gives a probability vector, composing two layers gives a
  layer, and the composite acts as the composition of the two steps.
* `l1dist_push_le` — a Markov step is `ℓ¹`-nonexpansive: attention never
  *increases* the discrepancy between two beliefs about position.
* `l1dist_push_le_of_min` — **Doeblin contraction**: if every entry of the layer
  is at least `ε`, one step contracts the `ℓ¹` distance by the factor `1 − mε`.
* `l1dist_push_attentionMatrix_le` — combined with the finite-temperature lower
  bound `scoreSoftmax_ge_of_spread` of `ChapterAttentionRetrieval`, a layer whose
  scores have spread at most `D` contracts by the factor `1 − e^{−βD} < 1`:
  **stacked attention forgets its input geometrically fast** unless the scores are
  allowed to spread with depth.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionMarkov

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterAttentionRetrieval

variable {m : ℕ}

/-! ## Stochastic matrices -/

/-- A matrix is **stochastic** when its entries are nonnegative and each row sums
to one. -/
def IsStochastic (P : Fin m → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- A vector is a **probability vector** when it is nonnegative and sums to one. -/
def IsProb (p : Fin m → ℝ) : Prop := (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1

/-- The **attention kernel**: row `i` is the Softmax of the score row `S i`. -/
def attentionMatrix (beta : ℝ) (S : Fin m → Fin m → ℝ) (i j : Fin m) : ℝ :=
  scoreSoftmax beta (S i) j

/-- Pushing a distribution over positions forward through a kernel. -/
def push (P : Fin m → Fin m → ℝ) (p : Fin m → ℝ) (j : Fin m) : ℝ := ∑ i, p i * P i j

/-- Composition of two kernels (the two-layer kernel). -/
def compose (P Q : Fin m → Fin m → ℝ) (i j : Fin m) : ℝ := ∑ k, P i k * Q k j

/-- The `ℓ¹` (total-variation-like) distance between two vectors. -/
def l1dist (p q : Fin m → ℝ) : ℝ := ∑ j, |p j - q j|

/-! ## The attention kernel is stochastic -/





/-! ## A Markov step preserves probability -/







/-! ## Stacking layers -/





/-! ## Contraction -/









end BookProof.ChapterAttentionMarkov

end


