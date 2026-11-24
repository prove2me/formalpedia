-- Prove2me | Definitions.Def_TailRiskSharing_VaRConv_Supplement_EllipticalProblem
-- name    : TailRiskSharing_VaRConv_Supplement_EllipticalProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:43:48.075236+00:00
-- url     : https://prove2.me/theorems/8d4874a9-1027-426d-88a2-f05b2d38f86c
-- title:
--   (24) — jointly elliptical feasible allocations and their infimum
-- statement:
--   Let $\mathcal X$ be a domain of real random variables, $X$ a total risk, and $\rho_1,\ldots,\rho_n$ real-valued risk measures. The feasible set consists of all allocations $(X_1,\ldots,X_n)$ in $\mathcal X^n$ whose sum is $X$ and whose joint law belongs to $\mathcal E_n(\psi)$. Define
--
--   $$V_\psi(X)=\inf\left\{\sum_{i=1}^n\rho_i(X_i):(X_1,\ldots,X_n)\in\mathcal A_n(X)\cap\mathcal E_n(\psi)\right\}.$$
--
--   Global optimality means membership in this entire feasible set and equality of the total risk with $V_\psi(X)$.
--
--   **Formalization Note** The value is an extended-real infimum rather than a minimum built into a definition. It is $+\infty$ on an empty feasible set and $-\infty$ for costs unbounded below. This exposes the attainment assertion of Theorem 5 for separate examination. Allocation sums reuse the published pointwise convention.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 22, (24)

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting
import Definitions.Def_TailRiskSharing_VaRConv_Supplement_Elliptical

namespace TailRiskSharing.VaRConv.Supplement

open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

/-- (24) p.22: feasible allocations jointly in E_n(ψ). -/
def EllipticalAllocations (P : Measure Ω) (dom : Set (Ω → ℝ)) (ψ : ℝ → ℂ)
    (n : ℕ) (X : Ω → ℝ) : Set (Fin n → Ω → ℝ) :=
  {Xs | Xs ∈ Allocations dom n X ∧ IsElliptical P ψ Xs}

/-- (24) p.22: the value as an extended-real infimum. Attainment is not built in. -/
noncomputable def ellipticalValue (P : Measure Ω) (dom : Set (Ω → ℝ)) (ψ : ℝ → ℂ)
    {n : ℕ} (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ) : EReal :=
  ⨅ Xs ∈ EllipticalAllocations P dom ψ n X, ((∑ i, ρ i (Xs i) : ℝ) : EReal)

/-- (24) p.22: global optimality among all jointly elliptical allocations. -/
def IsEllipticalOptimal (P : Measure Ω) (dom : Set (Ω → ℝ)) (ψ : ℝ → ℂ)
    {n : ℕ} (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ) (Xs : Fin n → Ω → ℝ) : Prop :=
  Xs ∈ EllipticalAllocations P dom ψ n X ∧
    ((∑ i, ρ i (Xs i) : ℝ) : EReal) = ellipticalValue P dom ψ ρ X

end TailRiskSharing.VaRConv.Supplement


