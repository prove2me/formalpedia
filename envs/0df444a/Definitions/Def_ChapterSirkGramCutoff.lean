-- Prove2me | Definitions.Def_ChapterSirkGramCutoff
-- name    : ChapterSirkGramCutoff
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T05:14:58.509986+00:00
-- url     : https://prove2.me/theorems/4cc2819f-487d-4188-bb89-2d53cfbd43ab
-- title:
--   `CONSOLIDATED_PLAN.md` §12.2, the recorded residue of **Gap 4c**.
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkGramCutoff`, source chapter `BookProof/ChapterSirkGramCutoff.lean`).
--
--   `CONSOLIDATED_PLAN.md` §12.2, the recorded residue of **Gap 4c**.
--
--   `BookProof/ChapterSirkGramWhitening.lean` quantifies the rank truncation of the SIRK/Hashimoto solver through a *geometric* parameter `δ`: if every raw (rational) Krylov vector `w i` sits within `δ` of the retained subspace, a reduced state loses at most `δ √m ‖c‖`. What was missing is the link between that `δ` and the quantity the code actually thresholds — the **eigenvalues of the Gram matrix** `G_{ij} = ⟪w i, w j⟫` that fall below the numerical cutoff (`rel_tol`) and are discarded.
--
--   This module supplies that link. With `u` an orthonormal eigenbasis of the Gram operator (what the Hermitian eigendecomposition returns), eigenvalues `lam`, and a retained index set `R` such that every *discarded* eigenvalue satisfies `lam k ≤ tol`, the whole defect is `√tol`.
--
--   * `IsGramEigen`, `exists_gramEigen` — the eigendecomposition of the Gram operator (it always exists: the operator is self-adjoint), `gramEigen_nonneg`, `inner_synthesis_gramEigen` (the synthesized eigenvectors are orthogonal with squared norms the eigenvalues) and `norm_sq_sum_orthogonal`. * `norm_sub_proj_le_of_mem_range` — for an isometric embedding `V`, the point `V V∗ x` of `range V` is the closest one; the projection property the defect estimate needs. * `dist_synthesis_retained_le` — **every state assembled from the raw vectors is within `√tol ‖c‖` of the retained subspace**. * `defect_le_sqrt_cutoff` — hence each raw vector `w i` is within `√tol` of it: the geometric parameter of `ChapterSirkGramWhitening` obeys `δ ≤ √tol`. * `sirk_end_to_end_truncated_cutoff` — the end-to-end SIRK bound with the additive truncation term `‖r(X)‖ √tol √m ‖c‖`, expressed purely through the numerical cutoff. * `retainedVec`, `retainedEmbedding` — the embedding the code builds from the retained eigenpairs, `V = W U_R Λ_R^{−1/2}` (the inverse-square-root whitening), with `retainedVec_orthonormal`, `retainedEmbedding_isometry` (`V∗V = 1`) and `range_retainedEmbedding` (its range is the retained subspace), so that `defect_le_sqrt_cutoff_retained` applies to the object the solver actually produces.
--
--   Everything is `sorry`-free and `axiom`-free.
--
--   **Boundary.** `tol` is here an exact bound on the discarded Gram eigenvalues; the floating-point analysis relating the *computed* eigenvalues to the exact ones (plan §12.2 Gap 6) is not addressed and stays out of scope.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGramCutoff.lean

import Definitions.Def_ChapterSirkGramWhitening
import Mathlib

import Mathlib

/-!
# Chapter SirkGramCutoff — the numerical Gram cutoff controls the truncation defect

`CONSOLIDATED_PLAN.md` §12.2, the recorded residue of **Gap 4c**.

`BookProof/ChapterSirkGramWhitening.lean` quantifies the rank truncation of the
SIRK/Hashimoto solver through a *geometric* parameter `δ`: if every raw (rational)
Krylov vector `w i` sits within `δ` of the retained subspace, a reduced state
loses at most `δ √m ‖c‖`.  What was missing is the link between that `δ` and the
quantity the code actually thresholds — the **eigenvalues of the Gram matrix**
`G_{ij} = ⟪w i, w j⟫` that fall below the numerical cutoff (`rel_tol`) and are
discarded.

This module supplies that link.  With `u` an orthonormal eigenbasis of the Gram
operator (what the Hermitian eigendecomposition returns), eigenvalues `lam`, and
a retained index set `R` such that every *discarded* eigenvalue satisfies
`lam k ≤ tol`, the whole defect is `√tol`.

## Deliverables

* `IsGramEigen`, `exists_gramEigen` — the eigendecomposition of the Gram operator
  (it always exists: the operator is self-adjoint), `gramEigen_nonneg`,
  `inner_synthesis_gramEigen` (the synthesized eigenvectors are orthogonal with
  squared norms the eigenvalues) and `norm_sq_sum_orthogonal`.
* `norm_sub_proj_le_of_mem_range` — for an isometric embedding `V`, the point
  `V V∗ x` of `range V` is the closest one; the projection property the defect
  estimate needs.
* `dist_synthesis_retained_le` — **every state assembled from the raw vectors is
  within `√tol ‖c‖` of the retained subspace**.
* `defect_le_sqrt_cutoff` — hence each raw vector `w i` is within `√tol` of it:
  the geometric parameter of `ChapterSirkGramWhitening` obeys `δ ≤ √tol`.
* `sirk_end_to_end_truncated_cutoff` — the end-to-end SIRK bound with the
  additive truncation term `‖r(X)‖ √tol √m ‖c‖`, expressed purely through the
  numerical cutoff.
* `retainedVec`, `retainedEmbedding` — the embedding the code builds from the
  retained eigenpairs, `V = W U_R Λ_R^{−1/2}` (the inverse-square-root
  whitening), with `retainedVec_orthonormal`, `retainedEmbedding_isometry`
  (`V∗V = 1`) and `range_retainedEmbedding` (its range is the retained
  subspace), so that `defect_le_sqrt_cutoff_retained` applies to the object the
  solver actually produces.

Everything is `sorry`-free and `axiom`-free.

**Boundary.** `tol` is here an exact bound on the discarded Gram eigenvalues; the
floating-point analysis relating the *computed* eigenvalues to the exact ones
(plan §12.2 Gap 6) is not addressed and stays out of scope.
-/

noncomputable section

namespace BookProof.ChapterSirkGramCutoff

open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## 1. Pythagoras for an orthogonal family -/



/-! ## 2. The eigendecomposition of the Gram operator -/

/-- `IsGramEigen w u lam` says that the orthonormal basis `u` diagonalizes the
Gram operator of the raw Krylov vectors `w` with eigenvalues `lam`: exactly the
output of the Hermitian eigendecomposition the solver performs. -/
def IsGramEigen {m : ℕ} (w : Fin m → E)
    (u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (lam : Fin m → ℝ) : Prop :=
  ∀ k, gramOp w (u k) = (lam k : ℂ) • u k



variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}







/-! ## 3. The projection property of an isometric embedding -/



/-! ## 4. The cutoff bounds the distance to the retained subspace -/











/-! ## 5. The embedding the code builds: `V = W U_R Λ_R^{−1/2}` -/

/-- The **retained, whitened Krylov vectors** `λ_k^{−1/2} W u_k` for the retained
eigenpairs listed by `e`: the columns of the inverse-square-root whitening the
solver forms from the Hermitian eigendecomposition of the Gram matrix. -/
def retainedVec {d : ℕ} (w : Fin m → E)
    (u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (lam : Fin m → ℝ)
    (e : Fin d → Fin m) : Fin d → E :=
  fun j => ((Real.sqrt (lam (e j)))⁻¹ : ℂ) • synthesis w (u (e j))



/-- The **retained embedding** `V = W U_R Λ_R^{−1/2}` the code builds. -/
def retainedEmbedding {d : ℕ} (w : Fin m → E)
    (u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (lam : Fin m → ℝ)
    (e : Fin d → Fin m) : EuclideanSpace ℂ (Fin d) →L[ℂ] E :=
  synthesis (retainedVec w u lam e)











end BookProof.ChapterSirkGramCutoff


