-- Prove2me | Definitions.Def_RobustBooking_Shared_value
-- name    : RobustBooking_Shared_value
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T08:15:23.892624+00:00
-- url     : https://prove2.me/theorems/12e40090-06c4-47ce-9405-4152f1d82586
-- title:
--   Reference price path (1) and value function $V(r_0)$ of the dynamic pricing problem: supremum of discounted profit over price sequences in $[0,\bar p]$
-- statement:
--   A monopolist charges a price $p_t$ from the interval $P=[0,\bar p]$ in every period $t=0,1,2,\dots$. Consumers carry a **reference price** $r_t$ that is updated by exponential smoothing,
--   $$
--   r_0 \text{ given},\qquad r_{t+1}=\alpha r_t+(1-\alpha)p_t ,
--   $$
--   with memory parameter $\alpha$ (equation (1) of the paper). The function $\mathrm{refPath}(\alpha,r_0,p)$ returns this sequence $(r_t)_{t\ge 0}$ for a given price sequence $p=(p_t)$.
--
--   Given a per-period profit $\Pi(p,r)$ and a discount factor $\beta$, the **value function** of the sequence problem is
--   $$
--   V(r_0)=\sup_{(p_t)\in P^{\mathbb N}}\ \sum_{t=0}^{\infty}\beta^t\,\Pi(p_t,r_t),\qquad r_{t+1}=\alpha r_t+(1-\alpha)p_t .
--   $$
--   The profit $\Pi$ is a parameter, so one definition serves the loss-neutral problem (2) and the kinked, convex-combination, loss and gain problems $(K)$, $(P_\theta)$, $(P_L)$, $(P_G)$ of Section 5.
--
--   **Formalization Note** The supremum is `⨆` over all sequences `ℕ → Set.Icc 0 pbar` (a nonempty index type when $\bar p\ge 0$) and the series is `tsum`. For $r_0\in P$ the reference path stays in $P$, which is convex, so under Assumption 1 (bounded, nonnegative demand) every series converges and the family of sums is bounded above. The real supremum is therefore the true supremum. $V$ is not assumed to solve the Bellman equation (2); that is a consequence.
--
--   **Shared definition.** Serves Popescu–Wu 2007 chunks `01-loss-aversion` (previously `ReferencePricing.LossAversion.value`) and `03-price-monotonicity` (previously `ReferencePricing.PriceMonotone.value`); both cite p. 417, Eq. (1) and the sequence problem defining $V(r_0)$. Chunk 03 uses it with $\mathrm{Prof}=\Pi$, the short-term profit $p\,D(p,r)$.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 417, Section 3, Eq. (1) and the sequence problem defining V(r_0)

import Mathlib

namespace RobustBooking.Shared

/-- The reference price formation mechanism (1) of Popescu and Wu (2007), p. 417:
`r_0 = r₀` and `r_{t+1} = α r_t + (1 − α) p_t` for a price sequence `p`. -/
def refPath (α r₀ : ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => r₀
  | t + 1 => α * refPath α r₀ p t + (1 - α) * p t

/-- The value function of the sequence problem on p. 417:
`V(r₀) = sup_{p_t ∈ P} ∑_{t ≥ 0} β^t Prof(p_t, r_t)` subject to (1), where `P = [0, p̄]`.
The supremum is over all price sequences with values in `P = Set.Icc 0 pbar` (a nonempty
index type); the per-period profit `Prof` is a parameter, so the same definition serves the
loss-neutral problem (2) and the problems (K), (P_θ), (P_L), (P_G) of §5.
For `r₀ ∈ P` the reference path stays in `P`, and under Assumption 1 the discounted sums are
summable and uniformly bounded, so this is the true supremum. -/
noncomputable def value (Prof : ℝ → ℝ → ℝ) (α β pbar r₀ : ℝ) : ℝ :=
  ⨆ p : ℕ → Set.Icc (0 : ℝ) pbar,
    ∑' t : ℕ, β ^ t * Prof (p t) (refPath α r₀ (fun s => (p s : ℝ)) t)

end RobustBooking.Shared


