-- Prove2me | Definitions.Def_ScholtesStab_MPCC_lagrangianS
-- name    : ScholtesStab_MPCC_lagrangianS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:14.789808+00:00
-- url     : https://prove2.me/theorems/1ff75c40-c737-4ae5-8c48-2dbe506da9c0
-- title:
--   Lagrange function $L^{\mathcal S}$ and tangent space $\mathcal T^{\mathcal S}_x$ of $\mathcal S$
-- statement:
--   For a Karush–Kuhn–Tucker point $x\in M^{\mathcal S}$ with multipliers $(\eta,\nu)$, the **Lagrange function** of $\mathcal S$ is
--
--   $$
--   L^{\mathcal S}(x)=f(x)-\sum_{j=1}^{\kappa}\eta_j\bigl(t-F_{1,j}(x)F_{2,j}(x)\bigr)-\sum_{j=1}^{\kappa}\nu_{1,j}F_{1,j}(x)-\sum_{j=1}^{\kappa}\nu_{2,j}F_{2,j}(x),
--   $$
--
--   and the corresponding **tangent space** is
--
--   $$
--   \mathcal T^{\mathcal S}_x=\Bigl\{\xi\in\mathbb R^n \Bigm| \bigl(F_{2,j}(x)DF_{1,j}(x)+F_{1,j}(x)DF_{2,j}(x)\bigr)\xi=0,\ j\in\mathcal H(x),\ \ DF_{1,j}(x)\xi=0,\ j\in\mathcal N_1(x),\ \ DF_{2,j}(x)\xi=0,\ j\in\mathcal N_2(x)\Bigr\}.
--   $$
--
--   **Formalization Note** `lagrangianS P t μ` is the function $x\mapsto L^{\mathcal S}(x)$ with all $\kappa$ constraints; `tangentSpaceS P t x` is the intersection of the kernels of the listed differentials.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.7

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_H
import Definitions.Def_ScholtesStab_MPCC_IsKKT

namespace ScholtesStab

namespace MPCC

variable {n κ : ℕ}

/-- **The Lagrange function `Lˢ` of S at a KKT point.**
Lämmel–Shikhman, arXiv:2501.07383v2, p.7: "For a Karush-Kuhn-Tucker point x ∈ Mˢ with
multipliers (η, ν) … it is convenient to define the appropriate Lagrange function as
Lˢ(x) = f(x) − Σⱼ ηⱼ (t − F₁,ⱼ(x)F₂,ⱼ(x)) − Σⱼ ν₁,ⱼ F₁,ⱼ(x) − Σⱼ ν₂,ⱼ F₂,ⱼ(x)."

**Formalization Note.** `lagrangianS P t μ` is the function `x ↦ Lˢ(x)`, with all `κ`
constraints and the multipliers `μ = (η, ν)`. -/
noncomputable def lagrangianS (P : MPCC n κ) (t : ℝ) (μ : SMult κ) : E n → ℝ :=
  fun x => P.f x - ∑ j, μ.η j * (t - P.F₁ j x * P.F₂ j x) - ∑ j, μ.ν₁ j * P.F₁ j x
    - ∑ j, μ.ν₂ j * P.F₂ j x

/-- **The tangent space `𝒯ˢ_x`** (p.7):
`𝒯ˢ_x = {ξ ∈ ℝⁿ | (F₂,ⱼ(x)DF₁,ⱼ(x) + F₁,ⱼ(x)DF₂,ⱼ(x))ξ = 0, j ∈ ℋ(x),
                    DF₁,ⱼ(x)ξ = 0, j ∈ 𝒩₁(x), DF₂,ⱼ(x)ξ = 0, j ∈ 𝒩₂(x)}`,
as the intersection of the kernels of the listed differentials. -/
noncomputable def tangentSpaceS (P : MPCC n κ) (t : ℝ) (x : E n) : Submodule ℝ (E n) :=
  (⨅ j ∈ P.H t x,
      LinearMap.ker (P.F₂ j x • fderiv ℝ (P.F₁ j) x + P.F₁ j x • fderiv ℝ (P.F₂ j) x).toLinearMap) ⊓
    (⨅ j ∈ P.N1 x, LinearMap.ker (fderiv ℝ (P.F₁ j) x).toLinearMap) ⊓
    ⨅ j ∈ P.N2 x, LinearMap.ker (fderiv ℝ (P.F₂ j) x).toLinearMap

end MPCC

end ScholtesStab


