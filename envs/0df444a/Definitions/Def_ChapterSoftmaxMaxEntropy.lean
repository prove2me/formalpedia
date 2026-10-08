-- Prove2me | Definitions.Def_ChapterSoftmaxMaxEntropy
-- name    : ChapterSoftmaxMaxEntropy
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T04:47:00.450069+00:00
-- url     : https://prove2.me/theorems/7b97e0fe-f7c9-4469-8444-73eac6241f1f
-- title:
--   Chapter SoftmaxMaxEntropy
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSoftmaxMaxEntropy.lean`): generated def bundle for ChapterSoftmaxMaxEntropy. See BookProof/ChapterSoftmaxMaxEntropy.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSoftmaxMaxEntropy.lean

import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxFluctuation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention" — Softmax as the maximum-entropy
attention

`ChapterAttentionEntropy` bounds the entropy of the attention distribution by
`log m` and computes its two extreme limits.  This module proves the *variational
characterisation* which explains why Softmax is the attention rule and not merely
a convenient one:

> Among **all** attention distributions with a prescribed mean alignment score,
> the Softmax distribution is the one of maximal Shannon entropy — it is the
> least committed distribution consistent with the observed alignment.

Deliverables:

* `crossEntropy` and `shannonEntropy_le_crossEntropy` — **Gibbs' inequality** in
  its general form: `H(p) ≤ -∑ⱼ pⱼ log qⱼ` for any probability vector `p` and any
  strictly positive sub-probability vector `q`.  (`ChapterAttentionEntropy`'s
  `shannonEntropy_le_log_card` is the uniform case.)
* `log_scoreSoftmax` — the Boltzmann form `log pⱼ(β) = β sⱼ − log Z(β)`;
* `shannonEntropy_scoreSoftmax` — the **thermodynamic identity**
  `H(β) = log Z(β) − β ⟨s⟩_β`;
* `shannonEntropy_le_of_meanScore_eq` — **the headline**: every probability
  distribution with the same mean score as `scoreSoftmax β s` has entropy at most
  `H(scoreSoftmax β s)`;
* `crossEntropy_scoreSoftmax` and `softmax_free_energy_le` — the equivalent free
  energy statement: Softmax minimises `β·⟨s⟩_p − H(p)` over all distributions `p`,
  the minimum being `−log Z(β)`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterSoftmaxMaxEntropy

open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
  BookProof.ChapterSoftmaxOrder BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

/-! ## Gibbs' inequality -/

/-- The **cross entropy** `-∑ⱼ pⱼ log qⱼ` of `p` relative to `q`. -/
def crossEntropy (p q : Fin m → ℝ) : ℝ := -∑ j, p j * Real.log (q j)



/-! ## The Boltzmann form of the attention weights -/







/-! ## The maximum-entropy principle -/







end BookProof.ChapterSoftmaxMaxEntropy

end


