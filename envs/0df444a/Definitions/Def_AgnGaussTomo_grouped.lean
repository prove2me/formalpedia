-- Prove2me | Definitions.Def_AgnGaussTomo_grouped
-- name    : AgnGaussTomo_grouped
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:55.888525+00:00
-- url     : https://prove2.me/theorems/14bcf6cf-40b6-4a6b-86e3-7085d46a3f3b
-- title:
--   Quadrature matrices in the grouped order $(q_1,\dots,q_n,p_1,\dots,p_n)$
-- statement:
--   The paper orders the quadratures as $\hat{\mathbf R}=(\hat q_1,\dots,\hat q_n,\hat p_1,\dots,\hat p_n)$, with canonical commutation relations $[\hat{\mathbf R}_i,\hat{\mathbf R}_j]=i\Omega_{n,ij}$ and $\Omega_n=\begin{pmatrix}0&I\\-I&0\end{pmatrix}$. This definition re-indexes a $2n\times 2n$ matrix given in the interleaved order $(q_1,p_1,\dots,q_n,p_n)$ into the grouped order. Symplectic matrices and Williamson decompositions are stated in the grouped order.
--
--   **Formalization Note** A relabelling of the same quadratures, so operator norms, traces and the Loewner order are unchanged. Mathlib's symplectic group uses $J=-\Omega_n$, which defines the same group.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), §2.2, printed pp. 8–9 (PDF pp. 11–12)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Support50.P14 (InterleavedQuadrature)

namespace AgnGaussTomo

/-- The quadrature index of the grouped ordering `R̂ = (q̂₁, …, q̂ₙ, p̂₁, …, p̂ₙ)`: `inl j ↦ q̂_j = (j, 0)`,
`inr j ↦ p̂_j = (j, 1)` in the interleaved labels of `Support50.P14`. -/
def groupIdx {n : ℕ} : Fin n ⊕ Fin n → InterleavedQuadrature (Fin n)
  | Sum.inl j => (j, 0)
  | Sum.inr j => (j, 1)

/-- **A quadrature matrix in the paper's grouped ordering.** Arulandu, Chen, Chen, Li, Ma, *Finding
Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), §2.2, printed
p. 9 (PDF p. 12): "R̂ = (q̂₁, …, q̂ₙ, p̂₁, …, p̂ₙ)ᵀ", with `[R̂_i, R̂_j] = iΩ_{n,ij}` and
`Ω_n = [[0, I], [−I, 0]]` (p. 8).

`grouped V` re-indexes a matrix on the interleaved quadratures `Fin n × Fin 2` (the convention of
the published `GaussianAt`) by `Fin n ⊕ Fin n`, `inl` = positions, `inr` = momenta. Williamson
decompositions and symplectic matrices are stated in this ordering.

**Formalization Note.** A relabelling of the same `2n` quadratures; operator norms, traces and
the Loewner order are unchanged. Mathlib's `Matrix.symplecticGroup` on `Fin n ⊕ Fin n` uses
`J = [[0, −I], [I, 0]] = −Ω_n`, which defines the same group. -/
def grouped {n : ℕ} {R : Type} (V : Matrix (InterleavedQuadrature (Fin n))
    (InterleavedQuadrature (Fin n)) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  fun a b => V (groupIdx a) (groupIdx b)

end AgnGaussTomo


