-- Prove2me | Definitions.Def_BewleyGE_wealthOperator
-- name    : BewleyGE_wealthOperator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:17.719118+00:00
-- url     : https://prove2.me/theorems/562499a6-b9eb-445e-abd5-806f9f77c1c8
-- title:
--   Wealth operator $M$ (equation (2))
-- statement:
--   For a savings policy $g$ at prices $(p,r)$, the **wealth operator** maps a wealth distribution $\lambda$ to next period's distribution
--   $$
--   M\lambda(D)=\int\sum_{y\in\mathcal Y}e(y)\,\mathbf 1_D\big((1+r)g(a)+p\cdot y\big)\,\lambda(da),\tag{2}
--   $$
--   that is, the mixture with weights $e(y)$ of the images of $\lambda$ under $a\mapsto(1+r)g(a)+p\cdot y$.
--
--   **Formalization Note** Measures are Borel measures on $\mathbb R$; $M\lambda$ is written as $\sum_y e(y)\cdot\lambda\circ T_y^{-1}$, which agrees with (2) on every Borel set for measurable $g$.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, (2), p.8

import Mathlib
import Definitions.Def_BewleyGE_Economy

open MeasureTheory

namespace BewleyGE

/-- **Wealth operator** `M`, equation (2). Light, arXiv:1906.06810v2, (2), p.8:
`Mλ(D; p, r) = ∫_{A(p,r)} ∑_{y ∈ 𝒴} e(y) 1_D((1 + r) g(a, p, r) + p · y) λ(da; p, r)`.

`Mλ` is the next period's wealth distribution when today's is `λ`: the mixture, with weights
`e(y)`, of the images of `λ` under `a ↦ (1 + r) g a + p · y`.

**Formalization Note.** Measures live on `ℝ`; a distribution on `A(p, r)` is a measure on `ℝ`
giving `A(p, r)ᶜ` measure zero, and for such `λ` the integral over `A(p, r)` equals the integral
over `ℝ`. `Mλ` is written as `∑_{y} e(y) • λ.map (a ↦ (1 + r) g a + p · y)`, which agrees with (2)
on every Borel set when `g` is measurable. -/
noncomputable def wealthOperator {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ)
    (g : ℝ → ℝ) (ν : Measure ℝ) : Measure ℝ :=
  ∑ y ∈ E.Y, ENNReal.ofReal (E.e y) • ν.map (fun a => (1 + r) * g a + ∑ i, p i * y i)

end BewleyGE


