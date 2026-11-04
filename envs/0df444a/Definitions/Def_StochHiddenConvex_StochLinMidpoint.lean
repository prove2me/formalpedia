-- Prove2me | Definitions.Def_StochHiddenConvex_StochLinMidpoint
-- name    : StochHiddenConvex_StochLinMidpoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:55.160883+00:00
-- url     : https://prove2.me/theorems/aea1cdda-c69a-44f9-9c92-4a4c938938a9
-- title:
--   Stochastic linearity in midpoint
-- statement:
--   Let $S\subseteq\mathbb R$ be convex and $\{Y(x),x\in S\}$ a family of real random variables. The family is **stochastically linear in midpoint** if for any $x_1,x_2\in S$ there exist $\hat Y(x_1)$ and $\hat Y(x_2)$ defined on a common probability space such that
--
--   1. $\hat Y(x_i)\overset{d}{=}Y(x_i)$ for $i=1,2$, and
--   2. $\dfrac{\hat Y(x_1)+\hat Y(x_2)}{2}\le_{cv}Y\Big(\dfrac{x_1+x_2}{2}\Big)$,
--
--   where $\le_{cv}$ is the concave order: $\mathbb E\,\varphi(A)\le\mathbb E\,\varphi(B)$ for every concave $\varphi$. Assumption 2.1(c) asks this of $u_i\mapsto\phi_i(g_i^{-1}(u_i),\xi_i)$ on $\mathcal U_i$; it is the condition under which the reformulated objective $G$ is convex (Proposition 2.1).
--
--   **Formalization Note** $Y(x)$ is represented by its law, a measure on $\mathbb R$. The common probability space is encoded by the joint law $\pi$ of $(\hat Y(x_1),\hat Y(x_2))$, a probability measure on $\mathbb R\times\mathbb R$ with the prescribed marginals. $\le_{cv}$ is the published concave order `MDPFinance.StructuredModels.LEConcaveOrder` ($\int\varphi\,d\mu\le\int\varphi\,d\nu$ for concave $\varphi$ integrable under both).
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, footnote 1, p.9 (Definition 1 of Feng and Shanthikumar 2018); Assumption 2.1(c), p.9

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_StochasticOrders

open MeasureTheory

namespace StochHiddenConvex

/-- *Stochastic linearity in midpoint* (Chen, He, Hu & Ye, arXiv:2205.01774v3, footnote 1, p.9,
quoting Definition 1 of Feng and Shanthikumar 2018): a family `{Y(x), x ∈ S}` of random
variables, `S` convex, is stochastically linear in midpoint if for any `x₁, x₂ ∈ S` there exist
`Ŷ(x₁)`, `Ŷ(x₂)` on a common probability space with `Ŷ(xᵢ) =ᵈ Y(xᵢ)` and
`(Ŷ(x₁) + Ŷ(x₂))/2 ≤_cv Y((x₁ + x₂)/2)`.

Here `Y x` is the law of `Y(x)`, a measure on `ℝ`.

**Formalization Note.** The common probability space is encoded by the joint law `π` of
`(Ŷ(x₁), Ŷ(x₂))`, a probability measure on `ℝ × ℝ` with marginals `Y x₁`, `Y x₂`; any pair on a
common space has such a joint law and conversely. `≤_cv` is the published concave order
`MDPFinance.StructuredModels.LEConcaveOrder` (`∫ φ dμ ≤ ∫ φ dν` for every concave `φ`
integrable under both). -/
def StochLinMidpoint (S : Set ℝ) (Y : ℝ → Measure ℝ) : Prop :=
  ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
    π.map Prod.fst = Y x₁ ∧ π.map Prod.snd = Y x₂ ∧
    MDPFinance.StructuredModels.LEConcaveOrder (π.map (fun p => (p.1 + p.2) / 2))
      (Y ((x₁ + x₂) / 2))

end StochHiddenConvex


