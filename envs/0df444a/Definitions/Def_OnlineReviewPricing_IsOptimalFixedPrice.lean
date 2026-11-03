-- Prove2me | Definitions.Def_OnlineReviewPricing_IsOptimalFixedPrice
-- name    : OnlineReviewPricing_IsOptimalFixedPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:28:12.781373+00:00
-- url     : https://prove2.me/theorems/f79371d8-46ab-40b4-89f0-da123b0e2488
-- title:
--   Optimal fixed prices $p^{OFP}_T$ in an allowed set $P$
-- statement:
--   A price $c\in P$ is an **optimal fixed price** if the constant path $p(t)\equiv c$ earns at least as much as every other constant path with price in $P$:
--
--   $$
--   c\in\arg\max_{c'\in P}\int_0^T c'\,\lambda\bigl(c',n^{c'}(t)\bigr)\,dt .
--   $$
--
--   There can be several (footnote 7, p.13).
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.13, definition of OFP

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsFluidPath
import Definitions.Def_OnlineReviewPricing_fluidRevenue

namespace OnlineReviewPricing

/-- `c` is an optimal fixed price in `P`: an `arg max` of the fixed-price revenue over `P`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.13). -/
def IsOptimalFixedPrice (μ μ₀ : ℝ) (P : Set ℝ) (γ T c : ℝ) : Prop :=
  c ∈ P ∧ ∃ n, IsFluidPath μ μ₀ γ T (fun _ => c) n ∧
    ∀ c' ∈ P, ∀ n', IsFluidPath μ μ₀ γ T (fun _ => c') n' →
      fluidRevenue μ μ₀ γ T (fun _ => c') n' ≤ fluidRevenue μ μ₀ γ T (fun _ => c) n

end OnlineReviewPricing


