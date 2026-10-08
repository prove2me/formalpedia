-- Prove2me | Definitions.Def_ChapterAttentionCollision
-- name    : ChapterAttentionCollision
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:29:57.709298+00:00
-- url     : https://prove2.me/theorems/5dd1c746-053a-4e0d-bd04-9c1eb3eebfcd
-- title:
--   Chapter AttentionCollision
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionCollision.lean`): generated def bundle for ChapterAttentionCollision. See BookProof/ChapterAttentionCollision.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionCollision.lean

import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": how many keys is the head actually reading?

The Shannon entropy of `ChapterAttentionEntropy` measures the uncertainty of the
Born measurement in nats.  Practitioners usually want the same information as a
*count*: how many keys does a head effectively attend to?  The standard answer is
the **participation ratio** — the reciprocal of the collision probability

`P₂(p) = ∑ⱼ pⱼ²`,  `N_eff(p) = 1 / P₂(p)`,

which is the exponential of the Rényi-2 (collision) entropy `H₂ = −log P₂`.  This
module proves that this count behaves exactly as a count should.

* `collisionProb_le_one`, `inv_card_le_collisionProb` (Cauchy–Schwarz) —
  `1/m ≤ P₂ ≤ 1`, hence `one_le_effectiveSupport` and
  `effectiveSupport_le_card`: a head reads at least one and at most `m` keys.
* `collisionProb_uniform`, `effectiveSupport_uniform` — at infinite temperature
  the count is exactly `m`, and `effectiveSupport_scoreSoftmax_zero` says the same
  for the attention distribution at `β = 0`.
* `renyi2_le_shannonEntropy` — the Rényi-2 entropy never exceeds the Shannon
  entropy (a tangent-line/Jensen argument for `log`), so the participation ratio
  is a *conservative* count: `N_eff ≤ exp H`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionCollision

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterAttentionEntropy

variable {m : ℕ}

/-! ## The collision probability and the participation ratio -/

/-- The **collision probability** `P₂(p) = ∑ pⱼ²`: the chance that two independent
Born measurements return the same key. -/
def collisionProb (p : Fin m → ℝ) : ℝ := ∑ j, (p j) ^ 2

/-- The **participation ratio** `N_eff = 1/P₂`: the effective number of keys the
head is reading. -/
def effectiveSupport (p : Fin m → ℝ) : ℝ := 1 / collisionProb p

/-- The **Rényi-2 (collision) entropy** `H₂ = −log P₂`. -/
def renyi2 (p : Fin m → ℝ) : ℝ := -Real.log (collisionProb p)

















/-! ## Rényi-2 versus Shannon -/







/-! ## The attention distribution -/









end BookProof.ChapterAttentionCollision

end


