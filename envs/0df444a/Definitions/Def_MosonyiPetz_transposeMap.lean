-- Prove2me | Definitions.Def_MosonyiPetz_transposeMap
-- name    : MosonyiPetz_transposeMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:55.682195+00:00
-- url     : https://prove2.me/theorems/95eacb6d-2f0d-4515-bab7-c2cc155a631b
-- title:
--   The transpose map $T^\#(X)=D_1^{1/2}T^*(T(D_1)^{-1/2}XT(D_1)^{-1/2})D_1^{1/2}$ (eq. (6))
-- statement:
--   For a linear map $T:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ and a density $D_1$ with $D_1$, $T(D_1)$ positive definite, the **transpose** (Petz recovery map) $T^\#:\mathcal B(\mathcal K)\to\mathcal B(\mathcal H)$ is
--
--   $$T^\#(X)=D_1^{1/2}\,T^*\big(T(D_1)^{-1/2}XT(D_1)^{-1/2}\big)\,D_1^{1/2},$$
--
--   where $T^*$ is the Hilbert–Schmidt adjoint of $T$. It is the standard dual of $\alpha$ and depends on $D_1$ (p.4: "the definition of $T^\#$ depends on the density $D_1$").
--
--   **Formalization Note** $T^*$ is the published `channelAdjoint`: $(T^*X)_{ij}=\sum_{k,l}\overline{T(E_{ij})_{kl}}\,X_{kl}$, so that $\operatorname{Tr}(T^*X)^*A=\operatorname{Tr}X^*T(A)$. Square roots as for $\alpha$.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, eq. (6), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

open scoped Matrix
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

namespace MosonyiPetz

/-- **The transpose map T#, eq. (6).**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, eq. (6), p.4: "T#(X) = D₁^{1/2} T*(T(D₁)^{−1/2} X T(D₁)^{−1/2}) D₁^{1/2}", the standard dual of
α; "the definition of T# depends on the density D1".

`transposeMap T D₁ X = D₁^{1/2} * T*(T(D₁)^{-1/2} * X * T(D₁)^{-1/2}) * D₁^{1/2}`, where `T*` is
the adjoint of `T` for the Hilbert–Schmidt inner product `⟨A, B⟩ = Tr A*B` (p.3).

**Formalization Note.** `T*` is `channelAdjoint T` (published bundle
`QAlgorithms.Papers.Independent.Dependency50.P21`): `(T* X)_{ij} = Σ_{k,l} conj (T(E_{ij}))_{kl} X_{kl}`,
i.e. `Tr ((T* X)ᴴ A) = Tr (Xᴴ T(A))`. Square roots are `cfc Real.sqrt` and `cfc (√·)⁻¹`. -/
noncomputable def transposeMap {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]
    [DecidableEq K] (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (D₁ : Matrix H H ℂ)
    (X : Matrix K K ℂ) : Matrix H H ℂ :=
  cfc Real.sqrt D₁ *
    channelAdjoint T (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (T D₁) * X *
      cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (T D₁)) * cfc Real.sqrt D₁

end MosonyiPetz


