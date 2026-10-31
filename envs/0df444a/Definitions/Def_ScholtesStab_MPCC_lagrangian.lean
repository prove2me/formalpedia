-- Prove2me | Definitions.Def_ScholtesStab_MPCC_lagrangian
-- name    : ScholtesStab_MPCC_lagrangian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:16.819917+00:00
-- url     : https://prove2.me/theorems/9c1648c3-acbe-4dd5-8b07-a100e42510fa
-- title:
--   Lagrange function $L$ and tangent space $\mathcal T_{\bar x}$ of MPCC
-- statement:
--   For a W-stationary point $\bar x\in M$ with multipliers $(\bar\sigma,\bar\varrho)$, the **Lagrange function** of MPCC is
--
--   $$
--   L(x)=f(x)-\sum_{j\in a_{01}(\bar x)}\bar\sigma_{1,j}F_{1,j}(x)-\sum_{j\in a_{10}(\bar x)}\bar\sigma_{2,j}F_{2,j}(x)-\sum_{j\in a_{00}(\bar x)}\bigl(\bar\varrho_{1,j}F_{1,j}(x)+\bar\varrho_{2,j}F_{2,j}(x)\bigr),
--   $$
--
--   and the corresponding **tangent space** is
--
--   $$
--   \mathcal T_{\bar x}=\{\xi\in\mathbb R^n \mid DF_{1,j}(\bar x)\xi=0,\ j\in a_{01}(\bar x)\cup a_{00}(\bar x),\quad DF_{2,j}(\bar x)\xi=0,\ j\in a_{10}(\bar x)\cup a_{00}(\bar x)\}.
--   $$
--
--   The restricted Hessian $D^2L(\bar x)\restriction_{\mathcal T_{\bar x}}$ defines the nondegeneracy condition NDC3 and the quadratic index of $\bar x$.
--
--   **Formalization Note** `lagrangian P x̄ m` is the function $x\mapsto L(x)$ (index sets taken at the base point $\bar x$); `tangentSpace P x̄` is the intersection of the kernels of the listed differentials.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.6

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_a01
import Definitions.Def_ScholtesStab_MPCC_IsCStationary

namespace ScholtesStab

namespace MPCC

variable {n κ : ℕ}

/-- **The Lagrange function `L` of MPCC at a W-stationary point.**
Lämmel–Shikhman, arXiv:2501.07383v2, p.6: "For a W-stationary point x̄ ∈ M with multipliers
(σ̄, ϱ̄) … it is convenient to define the appropriate Lagrange function as
L(x) = f(x) − Σ_{j∈a₀₁(x̄)} σ̄₁,ⱼ F₁,ⱼ(x) − Σ_{j∈a₁₀(x̄)} σ̄₂,ⱼ F₂,ⱼ(x)
       − Σ_{j∈a₀₀(x̄)} (ϱ̄₁,ⱼ F₁,ⱼ(x) + ϱ̄₂,ⱼ F₂,ⱼ(x))."

**Formalization Note.** `lagrangian P x̄ m` is the function `x ↦ L(x)`; the index sets are those
of the base point `x̄`, the multipliers are `m`. -/
noncomputable def lagrangian (P : MPCC n κ) (xbar : E n) (m : MPCCMult κ) : E n → ℝ :=
  fun x => P.f x - ∑ j ∈ P.a01 xbar, m.σ₁ j * P.F₁ j x - ∑ j ∈ P.a10 xbar, m.σ₂ j * P.F₂ j x
    - ∑ j ∈ P.a00 xbar, (m.ϱ₁ j * P.F₁ j x + m.ϱ₂ j * P.F₂ j x)

/-- **The tangent space `𝒯_x̄`** (p.6):
`𝒯_x̄ = {ξ ∈ ℝⁿ | DF₁,ⱼ(x̄)ξ = 0, j ∈ a₀₁(x̄) ∪ a₀₀(x̄), DF₂,ⱼ(x̄)ξ = 0, j ∈ a₁₀(x̄) ∪ a₀₀(x̄)}`,
as the intersection of the kernels of the listed differentials. -/
noncomputable def tangentSpace (P : MPCC n κ) (xbar : E n) : Submodule ℝ (E n) :=
  (⨅ j ∈ P.a01 xbar ∪ P.a00 xbar, LinearMap.ker (fderiv ℝ (P.F₁ j) xbar).toLinearMap) ⊓
    ⨅ j ∈ P.a10 xbar ∪ P.a00 xbar, LinearMap.ker (fderiv ℝ (P.F₂ j) xbar).toLinearMap

end MPCC

end ScholtesStab


