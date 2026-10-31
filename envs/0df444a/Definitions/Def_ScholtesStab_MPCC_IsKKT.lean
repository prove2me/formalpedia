-- Prove2me | Definitions.Def_ScholtesStab_MPCC_IsKKT
-- name    : ScholtesStab_MPCC_IsKKT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:10.958746+00:00
-- url     : https://prove2.me/theorems/bf8251eb-70f3-4b8d-ac56-d114fc63e1c8
-- title:
--   Karush–Kuhn–Tucker point of $\mathcal S$ with multipliers $(\eta,\nu)$
-- statement:
--   A feasible point $x\in M^{\mathcal S}$ of $\mathcal S$ is a **Karush–Kuhn–Tucker point** with multipliers $\eta_j,\nu_{1,j},\nu_{2,j}$, $j\in\{1,\dots,\kappa\}$, if
--
--   $$
--   Df(x)=-\sum_{j=1}^{\kappa}\eta_j\bigl(F_{2,j}(x)DF_{1,j}(x)+F_{1,j}(x)DF_{2,j}(x)\bigr)+\sum_{j=1}^{\kappa}\nu_{1,j}DF_{1,j}(x)+\sum_{j=1}^{\kappa}\nu_{2,j}DF_{2,j}(x) \tag{9}
--   $$
--
--   and, for every $j$,
--
--   $$
--   \eta_j\,(t-F_{1,j}(x)F_{2,j}(x))=0,\ F_{1,j}(x)F_{2,j}(x)\le t,\ \eta_j\ge0;\quad
--   \nu_{1,j}F_{1,j}(x)=0,\ F_{1,j}(x)\ge0,\ \nu_{1,j}\ge0;\quad
--   \nu_{2,j}F_{2,j}(x)=0,\ F_{2,j}(x)\ge0,\ \nu_{2,j}\ge0. \tag{10}
--   $$
--
--   **Formalization Note** The multipliers form a structure `SMult κ` of three functions `Fin κ → ℝ`. The paper's "KKT point" is $\exists$ multipliers with `IsKKT`.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.7, Definition 6, (9), (10)

import Mathlib
import Definitions.Def_ScholtesStab_MPCC

namespace ScholtesStab

/-- Multipliers `(η, ν) = (η, ν₁, ν₂)` of the Scholtes regularization S (p.7), indexed by
`j ∈ {1, …, κ}` (0-based `Fin κ`). -/
structure SMult (κ : ℕ) where
  /-- `ηⱼ`, multiplier of `F₁,ⱼ · F₂,ⱼ ≤ t` -/
  η : Fin κ → ℝ
  /-- `ν₁,ⱼ`, multiplier of `F₁,ⱼ ≥ 0` -/
  ν₁ : Fin κ → ℝ
  /-- `ν₂,ⱼ`, multiplier of `F₂,ⱼ ≥ 0` -/
  ν₂ : Fin κ → ℝ

namespace MPCC

variable {n κ : ℕ}

/-- **Definition 6 (Karush–Kuhn–Tucker point), with explicit multipliers.**
Lämmel–Shikhman, arXiv:2501.07383v2, p.7: "A feasible point x ∈ Mˢ of S is called
Kurush-Kuhn-Tucker [sic] point if there exist multipliers ηⱼ, ν₁,ⱼ, ν₂,ⱼ, j ∈ {1, …, κ}, such that
Df(x) = − Σⱼ ηⱼ (F₂,ⱼ(x)DF₁,ⱼ(x) + F₁,ⱼ(x)DF₂,ⱼ(x)) + Σⱼ ν₁,ⱼ DF₁,ⱼ(x) + Σⱼ ν₂,ⱼ DF₂,ⱼ(x)   (9)
ηⱼ (t − F₁,ⱼ(x) · F₂,ⱼ(x)) = 0, F₁,ⱼ(x) · F₂,ⱼ(x) ≤ t, ηⱼ ≥ 0,
ν₁,ⱼ F₁,ⱼ(x) = 0, F₁,ⱼ(x) ≥ 0, ν₁,ⱼ ≥ 0,
ν₂,ⱼ F₂,ⱼ(x) = 0, F₂,ⱼ(x) ≥ 0, ν₂,ⱼ ≥ 0, j ∈ {1, …, κ}."   (10)

`IsKKT P t x μ` says that `x ∈ Mˢ` (for the parameter `t`) and that `μ = (η, ν)` satisfies
(9) and (10).

**Formalization Note.** (9) is an equation of Fréchet derivatives `ℝⁿ →L[ℝ] ℝ`. The paper's
"KKT point" is `∃ μ, IsKKT P t x μ`. -/
def IsKKT (P : MPCC n κ) (t : ℝ) (x : E n) (μ : SMult κ) : Prop :=
  x ∈ P.MS t ∧
  fderiv ℝ P.f x =
      -(∑ j, μ.η j • (P.F₂ j x • fderiv ℝ (P.F₁ j) x + P.F₁ j x • fderiv ℝ (P.F₂ j) x))
        + ∑ j, μ.ν₁ j • fderiv ℝ (P.F₁ j) x + ∑ j, μ.ν₂ j • fderiv ℝ (P.F₂ j) x ∧
  ∀ j, (μ.η j * (t - P.F₁ j x * P.F₂ j x) = 0 ∧ P.F₁ j x * P.F₂ j x ≤ t ∧ 0 ≤ μ.η j) ∧
    (μ.ν₁ j * P.F₁ j x = 0 ∧ 0 ≤ P.F₁ j x ∧ 0 ≤ μ.ν₁ j) ∧
    (μ.ν₂ j * P.F₂ j x = 0 ∧ 0 ≤ P.F₂ j x ∧ 0 ≤ μ.ν₂ j)

end MPCC

end ScholtesStab


