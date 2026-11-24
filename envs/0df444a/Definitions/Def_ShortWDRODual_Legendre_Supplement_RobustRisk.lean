-- Prove2me | Definitions.Def_ShortWDRODual_Legendre_Supplement_RobustRisk
-- name    : ShortWDRODual_Legendre_Supplement_RobustRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:45:57.661157+00:00
-- url     : https://prove2.me/theorems/22bc61bf-4bae-4978-85cc-bcb5ed8ad851
-- title:
--   §5.2 — Kantorovich and maximum-cost robust risks
-- statement:
--   Let $\widehat P$ be the nominal probability law, $A$ the parameter domain, $f_\alpha$ the loss family, and $J(P)=\inf_{\alpha\in A}\mathbb E_P[f_\alpha]$. For a real radius $\rho$, define the two robust risks
--
--   $$\mathcal L_J(\rho)=\sup_{P\in\mathcal P(\mathcal X):\,\mathcal K_c(\widehat P,P)\le\rho}J(P),\qquad
--   \overline{\mathcal L}_J(\rho)=\sup_{P\in\mathcal P(\mathcal X):\,\overline{\mathcal K}_c(\widehat P,P)\le\rho}J(P).$$
--
--   The first cost is the published Kantorovich cost, with $c:\mathcal X\times\mathcal X\to[0,\infty]$. The second is the published infimum of coupling essential-supremum costs, using a finite real-valued cost that is nonnegative in Theorem 3(II). The nominal point is the first argument in each cost. These definitions retain the order $\sup_P\inf_\alpha$ and introduce no minimax assertion.
--
--   **Formalization Note** The costs, expectations and all extrema reuse the published extended-real conventions. Ball constraints compare in $\overline{\mathbb R}$, so a negative radius gives the empty supremum $-\infty$. An empty parameter domain gives $J(P)=+\infty$; an unbounded family of feasible risk values has supremum $+\infty$.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, §5.2, p. 11 (PDF p. 11)

import Mathlib
import Definitions.Def_ShortWDRODual_Legendre_Setting
import Definitions.Def_ShortWDRODual_MaxCost_Setting
import Definitions.Def_ShortWDRODual_Legendre_Supplement_RiskFunctional

namespace ShortWDRODual.Legendre.Supplement

open MeasureTheory

/-- The Kantorovich-ball robust risk of §5.2, p. 11: sup_P inf_a E_P[f_a].
The cost has nominal coordinate first and may equal +∞. Negative radii give -∞. -/
noncomputable def robustRisk {E X : Type*} [MeasurableSpace X]
    (A : Set E) (f : E → X → ℝ) (c : X → X → ENNReal)
    (Phat : Measure X) (rho : ℝ) : EReal :=
  ⨆ (P : Measure X)
    (_ : IsProbabilityMeasure P ∧ (RWPI.SqrtLasso.transportCost c Phat P : EReal) ≤ (rho : EReal)),
    riskFunctional A f P

/-- The maximum-cost-ball robust risk of §5.2, p. 11, with the overbar.
The real cost is nonnegative in Theorem 3(II); its definition is reused unchanged. -/
noncomputable def robustRiskMax {E X : Type*} [MeasurableSpace X]
    (A : Set E) (f : E → X → ℝ) (c : X → X → ℝ)
    (Phat : Measure X) (rho : ℝ) : EReal :=
  ⨆ (P : Measure X)
    (_ : IsProbabilityMeasure P ∧ (ShortWDRODual.MaxCost.maxCost c Phat P : EReal) ≤ (rho : EReal)),
    riskFunctional A f P

end ShortWDRODual.Legendre.Supplement


