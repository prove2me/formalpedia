-- Prove2me | Definitions.Def_ModelRiskOT_Duality_dualValue
-- name    : ModelRiskOT_Duality_dualValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:16:00.300992+00:00
-- url     : https://prove2.me/theorems/a92a9684-4cc9-4899-a141-2712e22c519f
-- title:
--   Dual objective $J(\lambda,\varphi)=\lambda\delta+\int\varphi\,d\mu$ and value $J$ (5)
-- statement:
--   Let $\mu$ be a probability measure on $S$ and $\delta>0$. For $\lambda\in\mathbb R$ and $\varphi:S\to[-\infty,\infty]$ the **dual objective** is
--
--   $$J(\lambda,\varphi)=\lambda\delta+\int\varphi\,d\mu\in[-\infty,\infty],$$
--
--   and the **dual value** is $J=\inf\{J(\lambda,\varphi):(\lambda,\varphi)\in\Lambda_{c,f}\}$.
--
--   For a dual-feasible pair, $\varphi(x)\ge f(x)$ (take $y=x$, $c(x,x)=0$), so $\int\varphi^-\,d\mu\le\int f^-\,d\mu<\infty$ and the integral involves no $\infty-\infty$.
--
--   **Formalization Note** $\int\varphi\,d\mu$ is `extIntegral`, i.e. $\int\varphi^+\,d\mu-\int\varphi^-\,d\mu$ with lower Lebesgue integrals, which for universally measurable $\varphi$ is the integral against the completion of $\mu$.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 6, definition of J(λ, φ) and Eq. (5)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ModelRiskOT_Duality_dualFeasible

namespace ModelRiskOT.Duality

open MeasureTheory

/-- The dual objective `J(λ, φ) = λδ + ∫ φ dμ` (Blanchet & Murthy, arXiv:1604.01446v2, p. 6),
in `EReal`, with `∫ φ dμ = ∫ φ⁺ dμ − ∫ φ⁻ dμ` (see `extIntegral`). For dual-feasible `(λ, φ)` one
has `φ ≥ f`, so `∫ φ⁻ dμ ≤ ∫ f⁻ dμ < ∞` and no `∞ − ∞` arises. -/
noncomputable def dualObj {S : Type*} [MeasurableSpace S] (μ : Measure S) (δ lam : ℝ)
    (φ : S → EReal) : EReal :=
  ((lam * δ : ℝ) : EReal) + extIntegral μ φ

/-- The dual value **(5)**, `J = inf {J(λ, φ) : (λ, φ) ∈ Λ_{c,f}}` (arXiv:1604.01446v2, p. 6),
an infimum in `EReal` over the dual feasible set (6b) (`dualFeasible c f Set.univ`). -/
noncomputable def dualValue {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (f : S → ℝ)
    (μ : Measure S) (δ : ℝ) : EReal :=
  ⨅ p ∈ dualFeasible c f Set.univ, dualObj μ δ p.1 p.2

end ModelRiskOT.Duality


