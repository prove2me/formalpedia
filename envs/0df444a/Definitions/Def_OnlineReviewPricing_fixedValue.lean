-- Prove2me | Definitions.Def_OnlineReviewPricing_fixedValue
-- name    : OnlineReviewPricing_fixedValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:28:21.835815+00:00
-- url     : https://prove2.me/theorems/c1358d22-1917-47a6-ac60-74aabea6b9e3
-- title:
--   Fixed-price revenue $\bar J^{OFP}_T$ over an allowed set $P$ of prices
-- statement:
--   For a set $P\subseteq\mathbb R$ of allowed prices, the **best fixed-price revenue** is
--
--   $$
--   \bar J^{OFP}_T=\sup_{c\in P}\ \bar J^{c}_T ,
--   $$
--
--   where $\bar J^c_T$ is the revenue of the constant price path $p(t)\equiv c$ along its fluid path. The optimal fixed-price policy (OFP) is the benchmark against which the dynamic optimum is measured.
--
--   **Formalization Note** The paper optimizes over $[\underline p,\bar p]$, which is the case $P=[\underline p,\bar p]$. A supremum is used so that $P$ can be any set.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.13, definition of OFP

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsFluidPath
import Definitions.Def_OnlineReviewPricing_fluidRevenue

namespace OnlineReviewPricing

/-- The best revenue of a fixed price in the allowed set `P`, the fluid revenue of OFP
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.13).

**Formalization Note.** The page optimizes over the interval `[p̲, p̄]`. Here the set `P ⊆ ℝ` is a
parameter, and `P = Set.Icc p̲ p̄` is the page's choice. Writing `sSup` for the page's `arg max`
needs no attainment for a general `P`. -/
noncomputable def fixedValue (μ μ₀ : ℝ) (P : Set ℝ) (γ T : ℝ) : ℝ :=
  sSup {J | ∃ c ∈ P, ∃ n, IsFluidPath μ μ₀ γ T (fun _ => c) n ∧
    J = fluidRevenue μ μ₀ γ T (fun _ => c) n}

end OnlineReviewPricing


