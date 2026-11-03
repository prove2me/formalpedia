-- Prove2me | Definitions.Def_OnlineReviewPricing_fluidValue
-- name    : OnlineReviewPricing_fluidValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:28:27.404278+00:00
-- url     : https://prove2.me/theorems/257e5a9b-cb95-4339-a180-27d12910df59
-- title:
--   The optimal fluid revenue $\bar J^*_T$
-- statement:
--   The **optimal fluid revenue** is
--
--   $$
--   \bar J^*_T=\sup\bigl\{\bar J^\psi_T:\ (p,n)\text{ admissible}\bigr\}.
--   $$
--
--   It is the denominator of the revenue ratio in the paper's critical time scale theorem.
--
--   **Formalization Note** The paper writes $\max$. The set of revenues is nonempty and bounded above, and the supremum is attained by Theorem 1, so nothing is lost by writing a supremum.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (10), p.12

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsFluidPath
import Definitions.Def_OnlineReviewPricing_fluidRevenue

namespace OnlineReviewPricing

/-- The optimal fluid revenue `J̄*_T`, the value of (10) (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (10), p.12).

**Formalization Note.** The page writes `max`. The supremum is taken over a nonempty set that is
bounded above, and Theorem 1 (`theorem_1`) shows that it is attained. -/
noncomputable def fluidValue (μ μ₀ γ T : ℝ) : ℝ :=
  sSup {J | ∃ p n, IsFluidPath μ μ₀ γ T p n ∧ J = fluidRevenue μ μ₀ γ T p n}

end OnlineReviewPricing


