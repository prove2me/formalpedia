-- Prove2me | Definitions.Def_ChapterSinusoidalPosition
-- name    : ChapterSinusoidalPosition
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T05:39:01.323375+00:00
-- url     : https://prove2.me/theorems/6e912c55-7dde-4b32-b1bf-9f9d3c721e1a
-- title:
--   Chapter SinusoidalPosition
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSinusoidalPosition.lean`): generated def bundle for ChapterSinusoidalPosition. See BookProof/ChapterSinusoidalPosition.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSinusoidalPosition.lean

import Definitions.Def_ChapterAttentionRetrieval
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": sinusoidal positions

`ChapterRotaryPosition` proves that the rotary encoding makes the alignment a
function of the *offset* of two positions.  The original sinusoidal encoding of a
transformer — a bank of sines and cosines at fixed frequencies — has the same
property, and this module proves it directly.

* `peInner_eq_sum_cos` — the alignment of two encoded positions is
  `∑ₐ cos(ωₐ(p − q))`: **it depends on the two positions only through their
  difference** (`peInner_shift`), so a head reading sinusoidally encoded positions
  is automatically translation-equivariant.
* `peInner_self`, `abs_peInner_le` — every encoded position has the same squared
  length `n`, and the alignment is bounded by `n`.
* `scoreSoftmax_sinusoidal_shift` — hence every attention weight is unchanged by a
  global shift of all positions, and `scoreSoftmax_sinusoidal_ge` gives the
  finite-temperature floor `e^{−2βn}/m` for the weight of every key.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterSinusoidalPosition

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterAttentionRetrieval

variable {n : ℕ}

/-- The **sinusoidal positional encoding** at frequencies `w`: the position `p` is
sent to the bank of pairs `(sin(ωₐp), cos(ωₐp))`. -/
def sinusoidalEncode (w : Fin n → ℝ) (p : ℝ) (a : Fin n) : ℝ × ℝ :=
  (Real.sin (w a * p), Real.cos (w a * p))

/-- The alignment (inner product) of two encoded positions. -/
def peInner (w : Fin n → ℝ) (p q : ℝ) : ℝ :=
  ∑ a, ((sinusoidalEncode w p a).1 * (sinusoidalEncode w q a).1
    + (sinusoidalEncode w p a).2 * (sinusoidalEncode w q a).2)











/-! ## Consequences for the attention weights -/





end BookProof.ChapterSinusoidalPosition

end


