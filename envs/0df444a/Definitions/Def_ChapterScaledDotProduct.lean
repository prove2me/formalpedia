-- Prove2me | Definitions.Def_ChapterScaledDotProduct
-- name    : ChapterScaledDotProduct
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:25:57.62392+00:00
-- url     : https://prove2.me/theorems/2d5f0446-4a44-488a-8072-afe1d5d0adab
-- title:
--   Chapter ScaledDotProduct
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterScaledDotProduct.lean`): generated def bundle for ChapterScaledDotProduct. See BookProof/ChapterScaledDotProduct.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScaledDotProduct.lean

import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": why the scores are divided by `√d`

Attention scores are dot products of `d`-dimensional vectors, and the standard
head divides them by `√d` before the Softmax.  The reason is a scaling law, and
this module proves it.

Take the query to be a random sign pattern `q ∈ {±1}^d` (the uniform Rademacher
model of "an unstructured query") and a fixed key `k`.  Then

* `rademacherMean_dot` — the raw score `⟨q,k⟩` has mean `0`, and
* `rademacherMean_dot_sq` — mean square `∑ᵢ kᵢ²`, i.e. `‖k‖²`.

So for a key with unit-size entries the score has root-mean-square `√d`
(`rademacherMean_dot_sq_of_unit_entries`): **the raw dot product grows like `√d`**.
Since `scoreSoftmax_div` shows that dividing every score by `c > 0` is exactly
dividing the inverse temperature by `c`, feeding raw scores to a Softmax at fixed
`β` is feeding scaled scores at the inverse temperature `β√d`, which diverges with
the model width — the head would freeze onto its arg-max as `d` grows.  Dividing
by `√d` (`rademacherMean_scaledDot_sq_of_unit_entries`: mean square exactly `1`)
holds the temperature fixed instead.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterScaledDotProduct

open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

/-! ## The Rademacher model -/

/-- The sign attached to a bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1





/-- The sign vector of a bit pattern: an unstructured `±1` query. -/
def signVec (x : Fin d → Bool) (i : Fin d) : ℝ := sgn (x i)

/-- The average of `f` over the `2^d` sign patterns. -/
def rademacherMean (f : (Fin d → Bool) → ℝ) : ℝ :=
  (∑ x : (Fin d → Bool), f x) / 2 ^ d

/-- The dot product of two coordinate vectors. -/
def dot (u v : Fin d → ℝ) : ℝ := ∑ i, u i * v i



/-! ## Flipping one coordinate -/

/-- Flipping the `i`-th bit. -/
def flipAt (i : Fin d) (x : Fin d → Bool) : Fin d → Bool := Function.update x i (!(x i))

theorem flipAt_involutive (i : Fin d) : Function.Involutive (flipAt (d := d) i) := by
  intro x
  funext j
  by_cases h : j = i
  · subst h; simp [flipAt]
  · simp [flipAt, Function.update_of_ne h]

/-- Flipping the `i`-th bit as a permutation of the sign patterns. -/
def flipEquiv (i : Fin d) : (Fin d → Bool) ≃ (Fin d → Bool) :=
  (flipAt_involutive i).toPerm _











/-! ## The mean and the mean square of a raw score -/









/-! ## The `1/√d` rescaling -/

/-- The scaled dot-product score of the standard attention head. -/
def scaledDot (u v : Fin d → ℝ) : ℝ := dot u v / Real.sqrt d



/-! ## Rescaling the scores is rescaling the temperature -/

variable {m : ℕ}





end BookProof.ChapterScaledDotProduct

end


