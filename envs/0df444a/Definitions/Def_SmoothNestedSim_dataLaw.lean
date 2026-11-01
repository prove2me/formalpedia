-- Prove2me | Definitions.Def_SmoothNestedSim_dataLaw
-- name    : SmoothNestedSim_dataLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:19.90135+00:00
-- url     : https://prove2.me/theorems/b6c62a7a-e9b0-459b-9746-d31f06c2c47b
-- title:
--   Law of the nested simulation data
-- statement:
--   Let $\mu_X$ be the law of $X$ and $\kappa$ the conditional law of the noise array given the design. The **nested simulation data** at sample sizes $(n,m)$ are the outer-level scenarios $\mathbf x_1,\dots,\mathbf x_n$, i.i.d. with law $\mu_X$, together with a noise array $(\epsilon_{ij})$ drawn from $\kappa(\mathbf x)$; the inner-level samples are $y_{ij}=f(\mathbf x_i)+\epsilon_{ij}$ (model (4)). Their joint law is
--
--   $$
--   \mu_X^{\otimes n}\otimes\kappa\quad\text{on }(\mathbb R^d)^n\times\mathbb R^{n\times m}.
--   $$
--
--   **Formalization Note** The data are represented by the pair (design, noise array) on this canonical space; only their law enters the stochastic-order statements.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §2.1, p.8; model (4), p.12

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SmoothNestedSim

/-- **The law of the nested simulation data** (Wang, Wang, Zhang, *Smooth Nested Simulation*,
arXiv:2201.02958v6, §2.1, p.8 and model (4), p.12): the outer-level scenarios `x₁, …, xₙ` are
i.i.d. with law `μX`, and given them the noise array `(ϵᵢⱼ)` has law `κ x`. The data point is
the pair `(x, ϵ)`; the inner-level samples are `yᵢⱼ = f(xᵢ) + ϵᵢⱼ` (4).

**Formalization Note.** The data at sample sizes `(n, m)` live on the canonical space
`(ℝ^d)ⁿ × ℝ^{n×m}` with law `μX^{⊗n} ⊗ κ` (Mathlib's composition-product `⊗ₘ`). Only the law of
the data enters the stochastic-order statements of the mission. -/
noncomputable def dataLaw {d n m : ℕ} (μX : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μX]
    (κ : Kernel (Fin n → EuclideanSpace ℝ (Fin d)) (Fin n → Fin m → ℝ)) :
    Measure ((Fin n → EuclideanSpace ℝ (Fin d)) × (Fin n → Fin m → ℝ)) :=
  (Measure.pi fun _ : Fin n => μX) ⊗ₘ κ

end SmoothNestedSim


