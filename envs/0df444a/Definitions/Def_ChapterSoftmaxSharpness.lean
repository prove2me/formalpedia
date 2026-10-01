-- Prove2me | Definitions.Def_ChapterSoftmaxSharpness
-- name    : ChapterSoftmaxSharpness
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T08:37:01.986165+00:00
-- url     : https://prove2.me/theorems/26cbf9e4-e4c2-40d7-9e4b-9669e96491ff
-- title:
--   Chapter SoftmaxSharpness
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSoftmaxSharpness.lean`): generated def bundle for ChapterSoftmaxSharpness. See BookProof/ChapterSoftmaxSharpness.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSoftmaxSharpness.lean

import Definitions.Def_ChapterSoftmaxBorn
import Mathlib


/-!
# Chapter "The Coherent State of Attention", §"The Divergence: Classical
Sharpness versus Quantum Flatness"

The opening section of `Book/CoherentState.lean` contrasts two candidate
attention rules on *classical points*:

* the **amplitude-squared (naive Born) rule**
  `P(q → k_j) = |⟪q,k_j⟫|² / ∑_l |⟪q,k_l⟫|²`, described as a "flat, polynomial
  curve"; and
* **Softmax**, `exp(β⟪q,k_j⟫) / ∑_l exp(β⟪q,k_l⟫)`, described as "sharp,
  winner-takes-all";

and it resolves the dichotomy by replacing the classical point with a coherent
state, where the Born rule *is* Softmax (`ChapterSoftmaxBorn`).  That section
carried no formal backing; this module supplies it, in the following precise
sense.

* `ampBorn_smul_query` — **flatness.**  The amplitude-squared rule is invariant
  under rescaling the query: `ampBorn (c • q) k = ampBorn q k` for every `c ≠ 0`.
  No amount of amplification sharpens it; in particular it has no temperature.
* `softmax_smul_query` — **sharpness is a temperature.**  Rescaling the query in
  Softmax is exactly a change of inverse temperature:
  `softmax β (c • q) k = softmax (β * c) q k`.
* `scoreSoftmax_zero` — at infinite temperature (`β = 0`) Softmax is the uniform
  distribution: maximal flatness.
* `tendsto_scoreSoftmax_max` / `tendsto_scoreSoftmax_ne` — **winner-takes-all.**
  If the scores have a strict maximizer `j`, then as `β → ∞` the Softmax weight
  of `j` tends to `1` and every other weight tends to `0`.
* `tendsto_coherentBorn_smul_query` — the resolution the chapter proposes, as a
  theorem: for keys of a common norm, the coherent-state Born weight of the
  strict maximizer tends to `1` as the query is amplified.  On coherent states
  the Born rule inherits Softmax's sharpening, which the classical
  amplitude-squared rule (`ampBorn_smul_query`) does not have.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterSoftmaxSharpness

open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

/-! ## The amplitude-squared rule is flat -/

/-- The **amplitude-squared (naive Born) attention rule** on classical points:
the dot products are read as probability amplitudes and normalized after
squaring. -/
def ampBorn (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (j : Fin m) : ℝ :=
  (inner ℝ q (k j)) ^ 2 / ∑ l, (inner ℝ q (k l)) ^ 2





/-! ## Softmax on abstract scores -/

/-- Softmax at inverse temperature `beta` applied directly to a family of real
scores. -/
def scoreSoftmax (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : ℝ :=
  Real.exp (beta * s j) / ∑ l, Real.exp (beta * s l)









/-! ## The zero-temperature limit: winner-takes-all -/









/-! ## The resolution: the coherent Born rule does sharpen -/





end BookProof.ChapterSoftmaxSharpness

end


