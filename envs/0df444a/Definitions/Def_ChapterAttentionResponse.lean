-- Prove2me | Definitions.Def_ChapterAttentionResponse
-- name    : ChapterAttentionResponse
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T07:18:50.765291+00:00
-- url     : https://prove2.me/theorems/8f479b63-7223-4027-b824-087bcbed52d9
-- title:
--   Chapter AttentionResponse
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionResponse.lean`): generated def bundle for ChapterAttentionResponse. See BookProof/ChapterAttentionResponse.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionResponse.lean

import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": how the output responds to temperature

`ChapterSoftmaxFluctuation` differentiates the attention *weights* in the inverse
temperature.  This module differentiates the **output** of the head, and finds the
vector-valued fluctuation–response law

`d/dβ  headOutput β s v  =  Cov(s, v)  =  ⟨s·v⟩ − ⟨s⟩·⟨v⟩`,

the covariance of the alignment score with the value vector under the current
attention distribution.

* `scoreValueCovariance` — the covariance vector, and `scoreValueCovariance_eq_sub`
  its familiar `⟨s v⟩ − ⟨s⟩⟨v⟩` form;
* `hasDerivAt_headOutput` / `deriv_headOutput` — **the response law**;
* `scoreValueCovariance_const` — a head whose values agree has zero response: with
  nothing to choose between, sharpening does nothing;
* `norm_scoreValueCovariance_le` — the response is bounded by (value bound) ×
  (score spread);
* `norm_headOutput_sub_le_temperature` — hence the whole temperature family is
  Lipschitz in `β`: `‖out(γ) − out(β)‖ ≤ C·(s_max − s_min)·|γ − β|`.

The last bound is the quantitative statement that an attention head cannot react
violently to a change of temperature unless its scores are genuinely spread out.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionResponse

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterSoftmaxFluctuation BookProof.ChapterObservableExpectation
  BookProof.ChapterAttentionOutput BookProof.ChapterSoftmaxTemperatureMonotone

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The score–value covariance -/

/-- The covariance of the alignment score with the value vector, under the
attention distribution at inverse temperature `beta`. -/
def scoreValueCovariance (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : E :=
  ∑ j, (scoreSoftmax beta s j * (s j - meanScore beta s)) • v j



/-! ## The response law -/







/-! ## Quantitative bounds -/







end BookProof.ChapterAttentionResponse

end


