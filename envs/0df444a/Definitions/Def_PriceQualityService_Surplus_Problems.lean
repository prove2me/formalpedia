-- Prove2me | Definitions.Def_PriceQualityService_Surplus_Problems
-- name    : PriceQualityService_Surplus_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:18:19.112261+00:00
-- url     : https://prove2.me/theorems/0c5fe293-0470-47ed-8df9-0a7787b3faa9
-- title:
--   Maximizers of the price-only, price-and-service, joint (4) and offer-set (10) problems
-- statement:
--   Fix duration bounds $t_s\le t_l$; a feasible duration vector lies in $[t_s,t_l]^N$. With the profit $\Pi$ of (3) and the offer-set profit $\Pi_S$ of (10), the module defines what it means to solve each of the firm's problems:
--
--   1. **Price only.** For pre-determined qualities $\mathbf q$ and durations $\mathbf t$, $\mathbf p^\dagger$ is optimal if $\Pi(\mathbf p',\mathbf q,\mathbf t)\le\Pi(\mathbf p^\dagger,\mathbf q,\mathbf t)$ for all $\mathbf p'\in\mathbb R^N$.
--   2. **Price and service duration.** For pre-determined $\mathbf q$, $(\mathbf p^\ddagger,\mathbf t^\ddagger)$ is optimal if $\mathbf t^\ddagger\in[t_s,t_l]^N$ and $\Pi(\mathbf p',\mathbf q,\mathbf t')\le\Pi(\mathbf p^\ddagger,\mathbf q,\mathbf t^\ddagger)$ for all $\mathbf p'\in\mathbb R^N$, $\mathbf t'\in[t_s,t_l]^N$.
--   3. **Price, quality and service duration** (problem (4)). $(\mathbf p^*,\mathbf q^*,\mathbf t^*)$ is optimal if $\mathbf t^*\in[t_s,t_l]^N$ and $\Pi(\mathbf p',\mathbf q',\mathbf t')\le\Pi(\mathbf p^*,\mathbf q^*,\mathbf t^*)$ for all $\mathbf p',\mathbf q'\in\mathbb R^N$, $\mathbf t'\in[t_s,t_l]^N$.
--   4. **Manufacturer's short-term problem** (10). For pre-determined $\mathbf q$, $(S,\mathbf p,\mathbf t)$ is optimal if $\mathbf t\in[t_s,t_l]^N$ and $\Pi_{S'}(\mathbf p',\mathbf q,\mathbf t')\le\Pi_S(\mathbf p,\mathbf q,\mathbf t)$ for every offer set $S'\subseteq\mathcal N$, $\mathbf p'\in\mathbb R^N$ and $\mathbf t'\in[t_s,t_l]^N$.
--
--   Optimality always means global maximality over the stated feasible set, never a first-order condition.
--
--   **Formalization Note** Qualities range over all of $\mathbb R$: the model's normalization $q_i\in[0,a_i/b_i)$ (p. 8) is not imposed in problem (4), whose solution in Theorem 1 is obtained over unconstrained qualities. In problem (10) the durations of products outside the offer set are also required to lie in $[t_s,t_l]$; they do not affect the profit.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 9 (PDF p. 9), problem (4); p. 13 (PDF p. 13), §2.3; pp. 20–21 (PDF pp. 20–21), problem (10); Online Supplement p. 1 (PDF p. 34)

import Mathlib
import Definitions.Def_PriceQualityService_Surplus_Profit

namespace PriceQualityService.Surplus

open Finset

/-- **Price-only optimization** (Wang, Ke & Cui, accepted manuscript (SSRN 3766191), p. 13 and
Online Supplement p. 1): with the qualities `q` and service durations `t` pre-determined, the
price vector `p` maximizes `Π(·, q, t; 𝒩)` over all of `ℝ^N`. -/
def IsPriceOptimal {N : ℕ} (α a b c s : Fin N → ℝ) (q t p : Fin N → ℝ) : Prop :=
  ∀ p' : Fin N → ℝ, PriceQualityService.Joint.profit α a b c s p' q t ≤ PriceQualityService.Joint.profit α a b c s p q t

/-- **Joint price and service-duration optimization** (p. 13, Online Supplement p. 1): with the
qualities `q` pre-determined, `(p, t)` maximizes `Π(·, q, ·; 𝒩)` over `p ∈ ℝ^N` and
`t ∈ [t_s, t_l]^N`; in particular `t` itself lies in `[t_s, t_l]^N`. -/
def IsPriceServiceOptimal {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (q p t : Fin N → ℝ) :
    Prop :=
  (∀ i, t i ∈ Set.Icc ts tl) ∧
    ∀ p' t' : Fin N → ℝ, (∀ i, t' i ∈ Set.Icc ts tl) →
      PriceQualityService.Joint.profit α a b c s p' q t' ≤ PriceQualityService.Joint.profit α a b c s p q t

/-- **Joint price, quality and service-duration optimization**, problem (4), p. 9: `(p, q, t)`
maximizes `Π(p, q, t; 𝒩)` over `p ∈ ℝ^N`, `q ∈ ℝ^N` and `t ∈ [t_s, t_l]^N`. Qualities range
over all of `ℝ` (the model's normalization `q_i ∈ [0, a_i/b_i)` of p. 8 is not imposed; the
paper's Theorem 1 maximizes over unconstrained qualities). -/
def IsJointOptimal {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (p q t : Fin N → ℝ) : Prop :=
  (∀ i, t i ∈ Set.Icc ts tl) ∧
    ∀ p' q' t' : Fin N → ℝ, (∀ i, t' i ∈ Set.Icc ts tl) →
      PriceQualityService.Joint.profit α a b c s p' q' t' ≤ PriceQualityService.Joint.profit α a b c s p q t

/-- **The manufacturer's short-term problem** (10), pp. 20–21: with the qualities `q`
pre-determined, the offer set `S ⊆ 𝒩`, the prices `p ∈ ℝ^N` and the durations
`t ∈ [t_s, t_l]^N` maximize the offer-set profit. -/
def IsOfferOptimal {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (q : Fin N → ℝ)
    (S : Finset (Fin N)) (p t : Fin N → ℝ) : Prop :=
  (∀ i, t i ∈ Set.Icc ts tl) ∧
    ∀ (S' : Finset (Fin N)) (p' t' : Fin N → ℝ), (∀ i, t' i ∈ Set.Icc ts tl) →
      offerProfit α a b c s S' p' q t' ≤ offerProfit α a b c s S p q t

end PriceQualityService.Surplus


