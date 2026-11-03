-- Prove2me | Definitions.Def_OnlineReviewPricing_IsOptimalPath
-- name    : OnlineReviewPricing_IsOptimalPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:28:25.72782+00:00
-- url     : https://prove2.me/theorems/7e21b8e6-9f65-42bb-9ab8-99f5783845c3
-- title:
--   Optimal paths of the fluid problem (10)
-- statement:
--   An admissible pair $(p,n)$ is **optimal** for the fluid problem
--
--   $$
--   \bar J^*_T=\max_{\psi\in\Psi}\bar J^\psi_T
--   \quad\text{subject to}\quad \dot n(t)=\lambda(p(t),n(t)),\ n(0)=0
--   $$
--
--   if its revenue is at least the revenue of every admissible pair.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (10), p.12

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsFluidPath
import Definitions.Def_OnlineReviewPricing_fluidRevenue

namespace OnlineReviewPricing

/-- `(p, n)` solves the fluid problem (10): it is admissible and its revenue is at least that of
every admissible pair (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (10), p.12). -/
def IsOptimalPath (μ μ₀ γ T : ℝ) (p n : ℝ → ℝ) : Prop :=
  IsFluidPath μ μ₀ γ T p n ∧
    ∀ p' n', IsFluidPath μ μ₀ γ T p' n' →
      fluidRevenue μ μ₀ γ T p' n' ≤ fluidRevenue μ μ₀ γ T p n

end OnlineReviewPricing


