-- Prove2me | Definitions.Def_AgnGaussTomo_IsWilliamson
-- name    : AgnGaussTomo_IsWilliamson
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:28.919445+00:00
-- url     : https://prove2.me/theorems/2bbcebfe-0d09-4e42-986d-8af5e58a7235
-- title:
--   Williamson decomposition $\hat V=S\hat DS^\top$
-- statement:
--   A **Williamson decomposition** of a real $2n\times2n$ matrix $\hat V$ is a factorization
--
--   $$
--   \hat V=S\,\hat D\,S^\top,\qquad \hat D=\operatorname{diag}(d_1,\dots,d_n,d_1,\dots,d_n),\quad d_j>0,
--   $$
--
--   with $S$ symplectic ($S\Omega_nS^\top=\Omega_n$). The $d_j$ are the symplectic eigenvalues. The unsqueezing step of Lemma 2.8 and the pure-state projection of Lemma 3.7 both start from such a decomposition of an estimated covariance.
--
--   **Formalization Note** Stated in the grouped quadrature order; symplectic means membership in `Matrix.symplecticGroup (Fin n) ℝ`. No ordering of the $d_j$ is required.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), §2.2, printed p. 8 (PDF p. 11); Lemma 2.8, p. 13 (PDF p. 16)

import Mathlib

namespace AgnGaussTomo

/-- **A Williamson decomposition `V̂ = S D̂ Sᵀ`.** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian
Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), §2.2, printed p. 8 (PDF
p. 11) and Lemma 2.8, p. 13: "Take a Williamson decomposition V̂ = S D̂ Sᵀ, where S is symplectic
and D̂ = diag(d₁, …, dₙ, d₁, …, dₙ) with d_j > 0".

`IsWilliamson Vhat S d` says that `S` is a real symplectic `2n × 2n` matrix, every `d_j > 0`, and
`Vhat = S · diag(d, d) · Sᵀ`, in the grouped ordering `(q̂₁, …, q̂ₙ, p̂₁, …, p̂ₙ)`.

**Formalization Note.** Symplectic means `S ∈ Matrix.symplecticGroup (Fin n) ℝ`, i.e.
`S J Sᵀ = J` with `J = [[0, −I], [I, 0]]`; since `J = −Ω_n` this is the paper's `S Ω_n Sᵀ = Ω_n`.
No ordering of the `d_j` is imposed (any decomposition counts). -/
def IsWilliamson {n : ℕ} (Vhat : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n → ℝ) : Prop :=
  S ∈ Matrix.symplecticGroup (Fin n) ℝ ∧ (∀ j, 0 < d j) ∧
    Vhat = S * Matrix.diagonal (Sum.elim d d) * S.transpose

end AgnGaussTomo


