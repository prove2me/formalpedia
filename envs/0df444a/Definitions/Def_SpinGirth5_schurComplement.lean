-- Prove2me | Definitions.Def_SpinGirth5_schurComplement
-- name    : SpinGirth5_schurComplement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:31.562121+00:00
-- url     : https://prove2.me/theorems/703a1eaf-0fce-4626-90c6-12e77aedb9d2
-- title:
--   Projected blocks $A_{ij}$ and the Schur complement $A/A_{00}$
-- statement:
--   Let $H$ be a finite-dimensional real inner-product space and $K_i,K_j\subseteq H$ subspaces. For a linear operator $A:H\to H$, its **projected block** is
--   $$A_{ij}:=\operatorname{proj}_{K_i}A|_{K_j}:K_j\to K_i .$$
--   For an orthogonal decomposition $H=H_0\oplus H_1$ with $H_1=H_0^{\perp}$ and $A_{00}$ invertible, the **Schur complement** of $A_{00}$ in $A$ is
--   $$A/A_{00}:=A_{11}-A_{10}A_{00}^{-1}A_{01}:H_1\to H_1 .$$
--   It is the effective operator on $H_1$ after the $H_0$-component has been chosen optimally, and it reduces positivity on $H_0\oplus H_1$ to positivity on $H_1$ (Proposition 14).
--
--   **Formalization Note** The projection is Mathlib's orthogonal projection onto a subspace. $A_{00}^{-1}$ is `Ring.inverse` in the ring of endomorphisms of $H_0$, which is the inverse whenever $A_{00}$ is invertible; every statement using the Schur complement assumes $A_{00}\succ 0$.
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, §2.3, Definition 13, Eq. (4), p.11; Definition 24, p.17

import Mathlib

namespace SpinGirth5

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The **projected block** `A_{ij} := proj_{K_i} A|_{K_j} : K_j → K_i` of a linear operator
`A : H → H` with respect to subspaces `K_i, K_j` of a finite-dimensional real inner-product space.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, §2.3, p.11 ("its blocks are A_ij := proj_{H_i} A|_{H_j} : H_j → H_i"),
and Definition 24, p.17.

**Formalization Note** `proj_{K_i}` is Mathlib's orthogonal projection
`Submodule.orthogonalProjectionOnto`, which exists for every subspace of a finite-dimensional
space. -/
noncomputable def block (A : H →ₗ[ℝ] H) (Ki Kj : Submodule ℝ H) : Kj →ₗ[ℝ] Ki :=
  (Ki.orthogonalProjectionOnto : H →L[ℝ] Ki).toLinearMap ∘ₗ A ∘ₗ Kj.subtype

/-- The **Schur complement** `A/A₀₀ := A₁₁ − A₁₀ A₀₀⁻¹ A₀₁ : H₁ → H₁` of the block `A₀₀` in `A`,
for the orthogonal decomposition `H = H₀ ⊕ H₁` with `H₁ := H₀ᗮ`.

Chen, Liu, arXiv:2608.25491, Definition 13 and Eq. (4), p.11: "Assume A00 is invertible. The
Schur complement of A00 in A is A/A00 := A11 − A10 A00⁻¹ A01."

**Formalization Note** `A₀₀⁻¹` is `Ring.inverse` in the ring `Module.End ℝ H₀`; it is the
inverse whenever `A₀₀` is invertible, which is the definition's standing assumption (every
statement using it assumes `A₀₀ ≻ 0`). Its junk value `0` on a non-invertible `A₀₀` is never
used. -/
noncomputable def schurComplement (A : H →ₗ[ℝ] H) (H₀ : Submodule ℝ H) :
    H₀ᗮ →ₗ[ℝ] H₀ᗮ :=
  block A H₀ᗮ H₀ᗮ - block A H₀ᗮ H₀ ∘ₗ (Ring.inverse (block A H₀ H₀) : Module.End ℝ H₀) ∘ₗ
    block A H₀ H₀ᗮ

end SpinGirth5


