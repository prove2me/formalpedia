-- Prove2me | Definitions.Def_matrix_completion_gram_schatten
-- name    : matrix_completion_gram_schatten
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-06-22T02:13:07.962466+00:00
-- url     : https://prove2.me/theorems/a8344924-da1d-4d2b-83c7-3997902efd1d
-- statement:
--   Diagonal-Gram Schatten norms for the coordinate Rademacher series of Candes-Recht 2009 Section 6.1. For the coordinate sampled matrices $A_{ij} = p^{-1}\delta_{ij} X_{ij} e_i e_j^\top$ the Gram sums are diagonal, so the Schatten-$q$ norm of $(\sum A A^\top)^{1/2}$ (resp. $(\sum A^\top A)^{1/2}$) equals the $\ell_q$ norm of the diagonal entries $p^{-1}\sqrt{\mathrm{rowEnergy}_i}$ (resp. $p^{-1}\sqrt{\mathrm{colEnergy}_j}$), where $\mathrm{rowEnergy}_i=\sum_j \delta_{ij} X_{ij}^2$ and $\mathrm{colEnergy}_j=\sum_i \delta_{ij} X_{ij}^2$. `sampledRowGramSchatten` and `sampledColumnGramSchatten` package these two $\ell_q$ quantities as reusable vocabulary.
-- source:
--   Candes, Recht, Exact matrix completion via convex optimization, arXiv:0805.4471, Section 6.1, Lemma 6.1, p.24.

import Definitions.Def_matrix_completion_rademacher

/-!
Diagonal-Gram Schatten norms for the coordinate Rademacher series of Section 6.1.

For the coordinate sampled matrices `A_ij = p⁻¹ δ_ij X_ij e_i e_jᵀ` appearing in the
noncommutative Khintchine inequality (Candès–Recht 2009, §6.1, Lemma 6.1), the Gram sums
are diagonal:
  `∑_{(i,j)} A_ij A_ijᵀ = diag_i (p⁻² · rowEnergy_i)`,
  `∑_{(i,j)} A_ijᵀ A_ij = diag_j (p⁻² · colEnergy_j)`,
where `rowEnergy_i = ∑_j δ_ij X_ij²` and `colEnergy_j = ∑_i δ_ij X_ij²`. Consequently the
Schatten-`q` norm of `(∑ A Aᵀ)^{1/2}` (resp. `(∑ Aᵀ A)^{1/2}`) equals the `ℓ_q` norm of the
diagonal entries `p⁻¹ √(rowEnergy_i)` (resp. `p⁻¹ √(colEnergy_j)`). These definitions package
those two `ℓ_q` quantities as reusable vocabulary, so the Khintchine right-hand side and its
`ℓ_q → ℓ_∞` comparison can both be stated directly.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- `ℓ_q`-norm of the per-row sampled Gram values `p⁻¹ √(rowEnergy_i)`; equals the Schatten-`q`
norm of the diagonal matrix `(∑_{(i,j)} A_ij A_ijᵀ)^{1/2}` for the coordinate sampled matrices
`A_ij = p⁻¹ δ_ij X_ij e_i e_jᵀ`. -/
noncomputable def sampledRowGramSchatten {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (q : Real) : Real :=
  Real.rpow
    (∑ i : Fin n1,
      Real.rpow (p⁻¹ * Real.sqrt (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) q)
    q⁻¹

/-- `ℓ_q`-norm of the per-column sampled Gram values `p⁻¹ √(colEnergy_j)`; equals the
Schatten-`q` norm of the diagonal matrix `(∑_{(i,j)} A_ijᵀ A_ij)^{1/2}`. -/
noncomputable def sampledColumnGramSchatten {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (q : Real) : Real :=
  Real.rpow
    (∑ j : Fin n2,
      Real.rpow (p⁻¹ * Real.sqrt (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) q)
    q⁻¹

end MatrixCompletion


