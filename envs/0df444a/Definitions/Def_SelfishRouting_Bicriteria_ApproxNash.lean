-- Prove2me | Definitions.Def_SelfishRouting_Bicriteria_ApproxNash
-- name    : SelfishRouting_Bicriteria_ApproxNash
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:17.164987+00:00
-- url     : https://prove2.me/theorems/5b8e03ac-1139-4b05-99e3-dd5d0837a234
-- title:
--   Definition 5.1, p. 19 — flows at $\epsilon$-approximate Nash equilibrium
-- statement:
--   In the model of the mission (routes with incidence matrix $A$, commodities, rates $r$, latencies $\ell$), let $\epsilon$ be a real number.
--
--   (**Definition 5.1**, p. 19.) The page reads: *A flow $f$ feasible for instance $(G, r, \ell)$ is at $\epsilon$-approximate Nash equilibrium if for all $i \in \{1,\dots,k\}$, $P_1, P_2 \in \mathcal P_i$, and $\delta \in [0, f_{P_1}]$, we have $\ell_{P_1}(f) \le (1+\epsilon)\ell_{P_2}(\tilde f)$,* where $\tilde f$ moves $\delta$ units from $P_1$ to $P_2$. Here: $f$ is at $\epsilon$-approximate Nash equilibrium if it is feasible for $r$ and, for every commodity $i$, every two **distinct** routes $P_1 \ne P_2$ in $\mathcal P_i$ and every $\delta$ with $0 < \delta \le f_{P_1}$,
--   $$
--   \ell_{P_1}(f) \le (1+\epsilon)\,\ell_{P_2}(\tilde f).
--   $$
--
--   It models users who switch routes only when the improvement exceeds a factor $1+\epsilon$. With $\epsilon = 0$ it is the Nash flow of Definition 2.1.
--
--   **Formalization Note.** The same two exclusions as in Definition 2.1 ($P_1 \ne P_2$ and $\delta > 0$) are made, for the same reasons. The section's standing assumption $\epsilon > 0$ (p. 19) is a hypothesis of the theorems, not part of the definition.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 19, Definition 5.1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model

namespace SelfishRouting.Bicriteria

open KellyStochasticNetworks

/-- **Definition 5.1** (p. 19): a route flow `x`, feasible for the rates `rate`, is at
`ε`-approximate Nash equilibrium if moving any amount `δ ∈ (0, x r₁]` of flow from a route `r₁`
to another route `r₂ ≠ r₁` of the same commodity gives `ℓ_{P₁}(f) ≤ (1 + ε) ℓ_{P₂}(f̃)`.
Same conventions as `IsNashFlow` (`δ > 0`, `r₁ ≠ r₂`). -/
def IsApproxNashFlow {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ) (ε : ℝ) (x : Fin R → ℝ) : Prop :=
  x ∈ wardropFeasible s rate ∧
    ∀ r₁ r₂ : Fin R, s r₁ = s r₂ → r₁ ≠ r₂ → ∀ δ : ℝ, 0 < δ → δ ≤ x r₁ →
      pathLatency A ℓ x r₁ ≤ (1 + ε) * pathLatency A ℓ (shiftFlow x r₁ r₂ δ) r₂

end SelfishRouting.Bicriteria


