-- Prove2me | Definitions.Def_ChapterAttentionOVCircuit
-- name    : ChapterAttentionOVCircuit
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T04:46:30.816565+00:00
-- url     : https://prove2.me/theorems/66e70879-4b06-431f-9d9c-080847c9746e
-- title:
--   Chapter AttentionOVCircuit
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionOVCircuit.lean`): generated def bundle for ChapterAttentionOVCircuit. See BookProof/ChapterAttentionOVCircuit.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionOVCircuit.lean

import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterAttentionQKCircuit
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": what the head writes

`ChapterAttentionQKCircuit` shows that the two learned projections on the *reading*
side of a head enter only through the single matrix `W_Qᵀ W_K`.  The same is true
on the *writing* side.  A head produces its contribution to the residual stream by
projecting each token down with a value map `W_V`, averaging with the attention
weights, and projecting back up with an output map `W_O`; because the average is
linear, the two matrices act only through their product `W_O W_V` — the *OV
circuit*.

* `mulVec_headOutput` — the head commutes with every linear map: averaging and then
  projecting is projecting and then averaging;
* `ovOutput_eq_headOutput` — **the headline**: the head's contribution is the
  attention average of the OV-transformed tokens, so only `W_O W_V` is observable;
* `ovOutput_congr_of_ovMatrix_eq` and `ovOutput_gauge` — two factorizations with the
  same product are indistinguishable, and `(W_O, W_V) ↦ (W_O A, B W_V)` with
  `A B = 1` is the head's `GL(d)` gauge freedom on the writing side;
* `rank_ovMatrix_le` — the OV circuit has rank at most the head dimension `d`;
* `ovOutput_mem_range` — so whatever the width of the stream, a head can only write
  into the (at most `d`-dimensional) column space of its output map.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionOVCircuit

open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterObservableExpectation BookProof.ChapterAttentionOutput

variable {d n p m : ℕ}

/-! ## The head commutes with linear maps -/



/-! ## The OV circuit -/

/-- The **OV circuit** of a head: the single matrix through which the value and
output projections act on the residual stream. -/
def ovMatrix (WO : Matrix (Fin n) (Fin d) ℝ) (WV : Matrix (Fin d) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := WO * WV

/-- The contribution a head writes back into the residual stream. -/
def ovOutput (beta : ℝ) (s : Fin m → ℝ) (WO : Matrix (Fin n) (Fin d) ℝ)
    (WV : Matrix (Fin d) (Fin n) ℝ) (x : Fin m → (Fin n → ℝ)) : Fin n → ℝ :=
  WO *ᵥ headOutput beta s (fun j => WV *ᵥ x j)









/-! ## The writing bottleneck -/





end BookProof.ChapterAttentionOVCircuit

end


