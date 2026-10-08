-- Prove2me | Definitions.Def_ChapterAttentionQKCircuit
-- name    : ChapterAttentionQKCircuit
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T02:15:59.857987+00:00
-- url     : https://prove2.me/theorems/f4539c22-2195-4468-a2b2-de72b7f256a0
-- title:
--   Chapter AttentionQKCircuit
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionQKCircuit.lean`): generated def bundle for ChapterAttentionQKCircuit. See BookProof/ChapterAttentionQKCircuit.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionQKCircuit.lean

import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": the head only sees one matrix

A head is usually written with two learned projections, a query map `W_Q` and a key
map `W_K`, and one is tempted to read them as two separate objects — "what the
token asks" and "what the token offers".  The score, however, is
`⟪W_Q x, W_K y⟫ = xᵀ(W_Qᵀ W_K)y`: the pair enters only through the single bilinear
form `W_Qᵀ W_K`, the *QK circuit*.  This module proves that this is exactly the
gauge freedom of the head.

* `qkScore_eq_bilinear` — the score is the bilinear form of `W_Qᵀ W_K`.
* `qkScore_congr_of_qkMatrix_eq` — two parameter pairs with the same product give
  the same scores, hence (`scoreSoftmax_qkScore_congr`, `headOutput_qkScore_congr`)
  the same attention weights and the same output: the split of the circuit into two
  factors is not observable.
* `qkScore_gauge` — **the headline**: for any `A, B` with `Aᵀ B = 1` (any invertible
  `A` with `B = (Aᵀ)⁻¹`), replacing `(W_Q, W_K)` by `(A W_Q, B W_K)` changes nothing.
  The parameters of a head are defined only up to this `GL(d)` action.
* `rank_qkMatrix_le` — the circuit has rank at most the head dimension `d`, which is
  the parameter-space source of the score-table bottleneck of
  `ChapterAttentionLowRank`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionQKCircuit

open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterObservableExpectation BookProof.ChapterAttentionOutput

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The QK circuit -/

/-- The **QK circuit** of a head: the single matrix through which the two learned
projections act on the scores. -/
def qkMatrix (WQ WK : Matrix (Fin d) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := WQᵀ * WK

/-- The raw score of a query token `x` against a key token `y`. -/
def qkScore (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x y : Fin n → ℝ) : ℝ :=
  (WQ *ᵥ x) ⬝ᵥ (WK *ᵥ y)





/-! ## The gauge freedom of a head -/





/-! ## What the head does with the scores -/







/-! ## The bottleneck lives in the circuit -/



end BookProof.ChapterAttentionQKCircuit


