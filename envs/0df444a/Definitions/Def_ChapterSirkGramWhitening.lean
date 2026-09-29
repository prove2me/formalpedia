-- Prove2me | Definitions.Def_ChapterSirkGramWhitening
-- name    : ChapterSirkGramWhitening
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T05:14:06.510491+00:00
-- url     : https://prove2.me/theorems/ab7732bf-8c4c-46b2-b7c3-22f791b6ec8a
-- title:
--   `CONSOLIDATED_PLAN.md` §12.2, **Gap 4c**. `BookProof/ChapterSirkWhitening.lean` proves that the reduced operator does no ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkGramWhitening`, source chapter `BookProof/ChapterSirkGramWhitening.lean`).
--
--   `CONSOLIDATED_PLAN.md` §12.2, **Gap 4c**. `BookProof/ChapterSirkWhitening.lean` proves that the reduced operator does not depend on *which* orthonormalization of the retained Krylov vectors is used — but every statement there is conditional on being handed an isometric embedding `V` (`V∗V = 1`) with the prescribed range. The numerics does not orthonormalize by an abstract construction: it forms the Gram matrix `G_{ij} = ⟪w_i, w_j⟫` of the raw (rational) Krylov vectors, diagonalizes it, and whitens with a `T` such that `T∗ G T = 1`.
--
--   This module closes that gap from below: it builds the objects the numerics uses and proves that they satisfy the hypotheses of `ChapterSirkWhitening`.
--
--   * `synthesis w` — the coefficient-to-state map `c ↦ ∑ i, c i • w i` of the raw Krylov vectors, with `range_synthesis`: its range is exactly the retained subspace `span{w₀, …, w_{m−1}}`. * `gramOp w = (synthesis w)∗ (synthesis w)` — the Gram operator, with `gramOp_apply` (its entries are the Gram matrix `⟪w i, w j⟫`), `gramOp_isSelfAdjoint`, `gramOp_nonneg`. * `IsWhitening w T` — the numerics' defining property `T∗ G T = 1`; `whitened w T` the resulting embedding. * `whitened_adjoint_comp_self` — **a whitening is an isometric embedding**, so every theorem of `ChapterSirkWhitening` applies to it; `range_whitened` — its range is the retained subspace as soon as `T` is surjective. * `exists_isWhitening` — **a whitening exists** for linearly independent Krylov vectors (the non-degenerate case), and `exists_isometry_range_eq_span` — an isometric embedding of the retained subspace exists in general, with reduced dimension equal to the rank (the exact, lossless rank truncation). * `sirkApprox_gram_whitening_eq`, `compress_gram_whitening_conj` — the end statements: the reconstructed SIRK operator is literally the same for any two whitenings of the same raw vectors, and the reduced `m × m` generators are unitarily conjugate, hence carry the same Ritz values. * Matrix layer: `gramMatrix`, `gramMatrix_conjTranspose`, `IsWhiteningMatrix` (`Mᴴ G M = 1`, what the code computes from the Hermitian eigendecomposition of `G`) and `isWhitening_of_matrix`. * `norm_defect_synthesis_le` — the quantified rank truncation: if every raw vector lies within `δ` of the retained subspace, a reduced state loses at most `δ √m ‖c‖`; and `sirk_end_to_end_truncated_gram`, the end-to-end bound with that term in place of the abstract defect of `ChapterSirkTruncation`.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
--
--   **Boundary.** The existence statement is about *some* whitening; the specific inverse-square-root factor the code uses is one such, and `ChapterSirkWhitening` shows the reduction does not depend on the choice. The near-degenerate case is covered only through the geometric parameter `δ` (the distance of the raw vectors to the retained subspace): no relation between `δ` and the discarded Gram eigenvalues, and no floating-point analysis, is claimed here.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGramWhitening.lean

import Definitions.Def_ChapterSirkWhitening
import Definitions.Def_ChapterSirkTruncation
import Mathlib

import Mathlib

/-!
# Chapter SirkGramWhitening — the Gram whitening exists and *is* an orthonormalization

`CONSOLIDATED_PLAN.md` §12.2, **Gap 4c**.  `BookProof/ChapterSirkWhitening.lean`
proves that the reduced operator does not depend on *which* orthonormalization of
the retained Krylov vectors is used — but every statement there is conditional on
being handed an isometric embedding `V` (`V∗V = 1`) with the prescribed range.
The numerics does not orthonormalize by an abstract construction: it forms the
Gram matrix `G_{ij} = ⟪w_i, w_j⟫` of the raw (rational) Krylov vectors,
diagonalizes it, and whitens with a `T` such that `T∗ G T = 1`.

This module closes that gap from below: it builds the objects the numerics uses
and proves that they satisfy the hypotheses of `ChapterSirkWhitening`.

## Deliverables

* `synthesis w` — the coefficient-to-state map `c ↦ ∑ i, c i • w i` of the raw
  Krylov vectors, with `range_synthesis`: its range is exactly the retained
  subspace `span{w₀, …, w_{m−1}}`.
* `gramOp w = (synthesis w)∗ (synthesis w)` — the Gram operator, with
  `gramOp_apply` (its entries are the Gram matrix `⟪w i, w j⟫`),
  `gramOp_isSelfAdjoint`, `gramOp_nonneg`.
* `IsWhitening w T` — the numerics' defining property `T∗ G T = 1`; `whitened w T`
  the resulting embedding.
* `whitened_adjoint_comp_self` — **a whitening is an isometric embedding**, so
  every theorem of `ChapterSirkWhitening` applies to it; `range_whitened` — its
  range is the retained subspace as soon as `T` is surjective.
* `exists_isWhitening` — **a whitening exists** for linearly independent Krylov
  vectors (the non-degenerate case), and `exists_isometry_range_eq_span` — an
  isometric embedding of the retained subspace exists in general, with reduced
  dimension equal to the rank (the exact, lossless rank truncation).
* `sirkApprox_gram_whitening_eq`, `compress_gram_whitening_conj` — the end
  statements: the reconstructed SIRK operator is literally the same for any two
  whitenings of the same raw vectors, and the reduced `m × m` generators are
  unitarily conjugate, hence carry the same Ritz values.
* Matrix layer: `gramMatrix`, `gramMatrix_conjTranspose`, `IsWhiteningMatrix`
  (`Mᴴ G M = 1`, what the code computes from the Hermitian eigendecomposition of
  `G`) and `isWhitening_of_matrix`.
* `norm_defect_synthesis_le` — the quantified rank truncation: if every raw
  vector lies within `δ` of the retained subspace, a reduced state loses at most
  `δ √m ‖c‖`; and `sirk_end_to_end_truncated_gram`, the end-to-end bound with
  that term in place of the abstract defect of `ChapterSirkTruncation`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).

**Boundary.** The existence statement is about *some* whitening; the specific
inverse-square-root factor the code uses is one such, and `ChapterSirkWhitening`
shows the reduction does not depend on the choice.  The near-degenerate case is
covered only through the geometric parameter `δ` (the distance of the raw vectors
to the retained subspace): no relation between `δ` and the discarded Gram
eigenvalues, and no floating-point analysis, is claimed here.
-/

noncomputable section

namespace BookProof.ChapterSirkGramWhitening

open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## 1. The synthesis map of the raw Krylov vectors -/

/-- The **synthesis map** `c ↦ ∑ i, c i • w i` of a finite family of vectors: the
map turning reduced coordinates into a state of the ambient space. -/
def synthesis {m : ℕ} (w : Fin m → E) : EuclideanSpace ℂ (Fin m) →L[ℂ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => ∑ i, c i • w i
      map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro r a; simp [smul_smul, Finset.smul_sum] }













/-! ## 2. The Gram operator -/

/-- The **Gram operator** `G = (synthesis w)∗ (synthesis w)` of the raw Krylov
vectors: the operator whose matrix in the coordinate basis is the Gram matrix. -/
def gramOp {m : ℕ} (w : Fin m → E) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  (ContinuousLinearMap.adjoint (synthesis w)).comp (synthesis w)









/-! ## 3. Whitenings -/

/-- The numerics' **whitening condition** `T∗ G T = 1` for the Gram operator `G`:
what the code enforces when it whitens with the inverse square root coming from
the Hermitian eigendecomposition of the Gram matrix. -/
def IsWhitening {m : ℕ} (w : Fin m → E)
    (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) : Prop :=
  (ContinuousLinearMap.adjoint T).comp ((gramOp w).comp T)
    = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m))

/-- The embedding built from the raw vectors and a whitening. -/
def whitened {m : ℕ} (w : Fin m → E)
    (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] E :=
  (synthesis w).comp T











/-! ## 4. Existence: an orthonormalization of the retained subspace -/



/-- The embedding attached to an orthonormal basis of a subspace. -/
def onbEmbedding {d : ℕ} (S : Submodule ℂ E) [CompleteSpace S]
    (b : OrthonormalBasis (Fin d) ℂ S) : EuclideanSpace ℂ (Fin d) →L[ℂ] E :=
  S.subtypeL.comp (b.repr.symm.toContinuousLinearMap)















/-! ## 5. The consequences for the reduction -/





/-! ## 6. The matrix layer -/

/-- The **Gram matrix** `G_{ij} = ⟪w i, w j⟫` the code actually forms. -/
def gramMatrix {m : ℕ} (w : Fin m → E) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟪w i, w j⟫_ℂ





/-- The matrix form of the whitening condition: `Mᴴ G M = 1`, exactly what the
code computes from the (rank-truncated) Hermitian eigendecomposition of `G`. -/
def IsWhiteningMatrix {m : ℕ} (w : Fin m → E) (M : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  Mᴴ * gramMatrix w * M = 1



/-! ## 7. Non-vacuity -/





/-! ## 8. Quantified rank truncation: how much a reduced state loses -/







end BookProof.ChapterSirkGramWhitening


