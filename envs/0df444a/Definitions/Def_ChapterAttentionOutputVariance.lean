-- Prove2me | Definitions.Def_ChapterAttentionOutputVariance
-- name    : ChapterAttentionOutputVariance
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:34:19.894034+00:00
-- url     : https://prove2.me/theorems/d141b678-5695-4e47-bbb4-03d1da882f38
-- title:
--   Chapter AttentionOutputVariance
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionOutputVariance.lean`): generated def bundle for ChapterAttentionOutputVariance. See BookProof/ChapterAttentionOutputVariance.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionOutputVariance.lean

import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": the uncertainty of the output

The attention output is the expectation value of the contextual observable, so it
carries the second moment of a measurement as well as the first.  This module
proves the elementary facts about that spread.

* `sum_dist_sq_eq` — the **bias–variance decomposition**: for any reference point
  `c`, `∑ⱼ pⱼ‖vⱼ − c‖² = Var(p,v) + ‖o − c‖²`, where `o` is the attention output.
* `observableExpectation_minimizes` — hence the head output is the *least-squares
  summary* of the values it is reading: no other vector is closer to the values in
  the attention-weighted mean-square sense.
* `outputVariance_eq_sub` (König–Huygens) and `norm_observableExpectation_sq_le` —
  `Var = ∑ pⱼ‖vⱼ‖² − ‖o‖² ≥ 0`, the Jensen inequality for the output norm.
* `outputVariance_eq_zero_iff_of_pos` — at a finite temperature every weight is
  positive, so the output carries *no* uncertainty exactly when all the values
  agree; `outputVariance_scoreSoftmax_eq_zero_iff` states this for the head.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace BookProof.ChapterAttentionOutputVariance

open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
  BookProof.ChapterSoftmaxOrder BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The attention-weighted variance of the values around the output. -/
def outputVariance (p : Fin m → ℝ) (v : Fin m → E) : ℝ :=
  ∑ j, p j * ‖v j - observableExpectation p v‖ ^ 2

















/-! ## The attention head -/







end BookProof.ChapterAttentionOutputVariance

end


