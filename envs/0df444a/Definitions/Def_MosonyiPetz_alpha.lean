-- Prove2me | Definitions.Def_MosonyiPetz_alpha
-- name    : MosonyiPetz_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:16.354922+00:00
-- url     : https://prove2.me/theorems/29d0387a-a17e-4635-a234-31e0a5fc4cf6
-- title:
--   The map $\alpha(A)=T(D_1)^{-1/2}T(D_1^{1/2}AD_1^{1/2})T(D_1)^{-1/2}$ (eq. (5))
-- statement:
--   For a linear map $T:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ and a density $D_1$ on $\mathcal H$ (with $D_1$ and $T(D_1)$ positive definite), the map $\alpha:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ is
--
--   $$\alpha(A)=T(D_1)^{-1/2}\,T\big(D_1^{1/2}AD_1^{1/2}\big)\,T(D_1)^{-1/2}.$$
--
--   It is linear in $A$. The paper introduces it as the dual of $T^*$ for the weighted inner products $\langle\cdot,\cdot\rangle_{D_1}$ and $\langle\cdot,\cdot\rangle_{T(D_1)}$ (eq. (4)); that characterization is the milestone `alpha_dual`.
--
--   **Formalization Note** $D^{1/2}$ and $D^{-1/2}$ are the continuous functional calculus of $\sqrt x$ and $(\sqrt x)^{-1}$; on the positive definite matrices to which the theorems apply them they are the positive square root and its inverse. The map depends on $D_1$ (p.4), which is an explicit argument.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, eq. (5), p.4

import Mathlib

open scoped Matrix

namespace MosonyiPetz

/-- **The map α, eq. (5).**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, eq. (5), p.4: "α(A) = T(D₁)^{−1/2} T(D₁^{1/2} A D₁^{1/2}) T(D₁)^{−1/2}", the dual of `T*`
for the weighted inner products of p.3 (eq. (4)).

`alpha T D₁` is the `ℂ`-linear map `Matrix H H ℂ → Matrix K K ℂ` sending `A` to
`T(D₁)^{-1/2} * T (D₁^{1/2} * A * D₁^{1/2}) * T(D₁)^{-1/2}`.

**Formalization Note.** The square root and the inverse square root are the continuous functional
calculus of the real functions `√x` and `(√x)⁻¹` (`cfc`). On the positive definite matrices to
which the theorems apply them (`D₁`, `T(D₁)`) these are the usual positive square root and its
inverse; on other inputs the value is irrelevant. As the paper notes (p.4), the map depends on
`D₁`, which is therefore an explicit argument. -/
noncomputable def alpha {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (D₁ : Matrix H H ℂ) :
    Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ where
  toFun A := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (T D₁) *
      T (cfc Real.sqrt D₁ * A * cfc Real.sqrt D₁) * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (T D₁)
  map_add' A B := by simp [mul_add, add_mul]
  map_smul' c A := by simp

end MosonyiPetz


