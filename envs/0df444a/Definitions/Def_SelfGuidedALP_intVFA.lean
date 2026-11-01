-- Prove2me | Definitions.Def_SelfGuidedALP_intVFA
-- name    : SelfGuidedALP_intVFA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:41.430744+00:00
-- url     : https://prove2.me/theorems/67ec70fb-310d-413d-8752-59a3706d4f18
-- title:
--   The integral value function approximation $V(s;\boldsymbol\beta)$ of (3)
-- statement:
--   For $\boldsymbol\beta=(\beta_0,B)$ with $B\in\mathcal B$, the **integral value function approximation** is
--   $$
--   V(s;\boldsymbol\beta):=\beta_0+\int_\Theta B(\theta)\,\varphi(s;\theta)\,\mathrm d\theta .
--   $$
--
--   The integral is finite: $\int_\Theta|B|\le\|B/\rho\|_{2,\rho}$ by Cauchy–Schwarz, and this integrability is proved in the mission's verification file.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, eq. (3), p.9

import Mathlib
import Definitions.Def_SelfGuidedALP_Bspace
import Definitions.Def_SelfGuidedALP_feat

open MeasureTheory

namespace SelfGuidedALP

/-- The integral value function approximation `V(s;𝛃) := β₀ + ∫_Θ B(θ) ϕ(s;θ) dθ` of eq. (3)
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, eq. (3), p.9). -/
noncomputable def intVFA {d : ℕ} (R : RBClass d) (β₀ : ℝ) (B : Bspace R)
    (s : EuclideanSpace ℝ (Fin d)) : ℝ :=
  β₀ + ∫ θ in R.Θ, B θ * feat R.ϕ θ s

end SelfGuidedALP


