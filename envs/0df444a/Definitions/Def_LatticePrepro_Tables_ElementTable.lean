-- Prove2me | Definitions.Def_LatticePrepro_Tables_ElementTable
-- name    : LatticePrepro_Tables_ElementTable
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:21:50.629249+00:00
-- url     : https://prove2.me/theorems/79a927fc-06ef-4b56-a760-9ea31429f91e
-- title:
--   Element polynomials $\ell_h$ and their products (Construction A.4, step 6)
-- statement:
--   Fix a field setup: a sample field $\mathbb{S}$ and an extension $K=\mathbb{S}(\gamma)$ in which every element is $f(\gamma)$ for some $f\in\mathbb{S}[X]$ of degree $<\delta$. Let $m$ and $B$ be natural numbers and $\alpha\in K$. The bundle defines:
--
--   1. **Element polynomials** (`elemPoly`): for $0\le h<m$, a polynomial $\ell_h\in\mathbb{S}[X]$ with
--      $$\deg\ell_h<\delta,\qquad \ell_h(\gamma)=\alpha^{B^h}.$$
--   2. **Products** (`elemProd`): for an exponent vector $\eta\in\mathbb{N}^m$, the polynomial
--      $$\prod_{h=0}^{m-1}\ell_h^{\eta_h}\in\mathbb{S}[X].$$
--
--   In step 6 of Construction A.4 these polynomials define the evaluation table $\hat e_\alpha$ of $\alpha$: in each column $s\in\mathbb{S}$ it has a single entry $1$, at the label $\lambda=(\ell_0(s),\dots,\ell_{m-1}(s))$. Its weighted column sums are the values $\prod_h\ell_h(s)^{\eta_h}$, so its interpolants are the products above. These have low degree and evaluate at $\gamma$ to $\alpha^{\mathrm{val}_B(\eta)}$, which gives the completeness part of Theorem A.8.
--
--   **Formalization Note**: $\ell_h$ is selected by choice from the field setup's property that every element of $K$ is a polynomial of degree $<\delta$ in $\gamma$. Since $1,\gamma,\dots,\gamma^{\delta-1}$ are $\mathbb{S}$-linearly independent, it is the unique such polynomial, as in the paper. The table $\hat e_\alpha$ itself (`elemTab`) is defined in the source module and is not part of this bundle. The paper writes $\varphi_h,\mathbf{q}_\alpha,c,\zeta,\mathsf d$ for $\ell_h,\hat e_\alpha,\delta,\gamma,B$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Construction A.4 (\label{con:moment-representation}), step 6 (\label{step:moment-element-table}); Lean: LatticePrepro/Tables/ElementTable.lean, LatticePrepro.ExplicitTables.elemPoly, LatticePrepro.ExplicitTables.elemProd

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Construction

/-!
# Evaluation tables of field elements (Construction A.4, step 6; completeness in Theorem A.8)

For `α ∈ K` and `h < m`, let `ℓ_h ∈ 𝕊[X]` be the polynomial of degree `< δ` with
`ℓ_h(γ) = α^{B^h}`. The *element table* `ê_α` has a single `1` in every column `s`, at the label
`λ = (ℓ_0(s), …, ℓ_{m-1}(s))`. Its column sums are `∏_h ℓ_h(s)^{η_h}`, so its interpolants are the
low-degree polynomials `∏_h ℓ_h^{η_h}`, and its moments are `α^k`.
-/

namespace LatticePrepro

open Polynomial

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

/-- The polynomial `ℓ_h` with `ℓ_h(γ) = α^{B^h}` and degree `< δ`. -/
noncomputable def elemPoly (α : FS.K) (h : Fin m) : FS.𝕊[X] :=
  (FS.exists_aeval (α ^ B ^ (h : ℕ))).choose

/-- The product polynomial `∏_h ℓ_h^{η_h}`. -/
noncomputable def elemProd (α : FS.K) (η : Fin m → ℕ) : FS.𝕊[X] :=
  ∏ h, elemPoly FS m B α h ^ η h

variable {FS m B}

end ExplicitTables

end LatticePrepro


