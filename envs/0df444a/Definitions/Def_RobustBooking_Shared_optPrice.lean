-- Prove2me | Definitions.Def_RobustBooking_Shared_optPrice
-- name    : RobustBooking_Shared_optPrice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T08:32:41.687049+00:00
-- url     : https://prove2.me/theorems/31a19d78-4959-402c-bb39-432ff03469f8
-- title:
--   Bellman objective $W(p,r)$ (2), optimal (largest-maximizer) pricing policy $p^*(r)$, reference policy $q^*(r)$, optimal paths and steady states
-- statement:
--   Fix a per-period profit $\Pi(p,r)$, memory $\alpha$, discount factor $\beta$ and price ceiling $\bar p$, and let $V$ be the value function of the sequence problem on $P=[0,\bar p]$. This file defines the objects of Section 3 of the paper.
--
--   1. The **Bellman objective** of equation (2):
--   $$
--   W(p,r)=\Pi(p,r)+\beta\,V(\alpha r+(1-\alpha)p).
--   $$
--   2. The **optimal pricing policy** $p^*(r)=\arg\max_{p\in P}W(p,r)$, where, as in the paper, $\arg\max$ denotes the *largest* maximizer. It is defined as the supremum of the set of maximizers of $W(\cdot,r)$ over $P$.
--   3. The **optimal reference price policy** $q^*(r)=\alpha r+(1-\alpha)p^*(r)$.
--   4. The **state path** $r^*_0=r_0$, $r^*_{t+1}=q^*(r^*_t)$, and the **pricing path** $p^*_t=p^*(r^*_t)$.
--   5. A **steady state** is a price $p^{**}\in P$ with $p^*(p^{**})=p^{**}$. Then $q^*(p^{**})=p^{**}$ as well, so the optimal price path from $r_0=p^{**}$ is constant.
--
--   These definitions are generic in $\Pi$ and are used for the smooth problem (2) and for the problems $(K)$, $(P_\theta)$, $(P_L)$, $(P_G)$.
--
--   **Formalization Note** The largest maximizer is `sSup` of the argmax set. That set is a subset of $P$, and under the paper's hypotheses it is nonempty and compact. This is a proof obligation of the theorems that use it, never a hypothesis. On an empty set `sSup` returns $0$, which is why no theorem of the mission assumes anything about the argmax.
--
--   **Shared definition.** Serves Popescu–Wu 2007 chunks `01-loss-aversion` (previously `ReferencePricing.LossAversion.optPrice`) and `03-price-monotonicity` (previously `ReferencePricing.PriceMonotone.optPrice`); both cite p. 417, Eq. (2), the policies $p^*(r)$, $q^*(r)$, the state and pricing paths and the steady state.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 417, Eq. (2) and the definitions of p*(r), q*(r), the pricing path, the state path and the steady state

import Mathlib
import Definitions.Def_RobustBooking_Shared_value

namespace RobustBooking.Shared

/-- The Bellman objective of (2), p. 417: `W(p, r) = Prof(p, r) + β V(α r + (1 − α) p)`,
with `V` the sequence-problem value function `value`. -/
noncomputable def bellmanObj (Prof : ℝ → ℝ → ℝ) (α β pbar p r : ℝ) : ℝ :=
  Prof p r + β * value Prof α β pbar (α * r + (1 - α) * p)

/-- The optimal pricing policy `p*(r) = argmax_{p ∈ P} W(p, r)`, p. 417, where
"argmax refers … to the largest maximizer": the supremum of the set of maximizers of
`W(·, r)` over `P = [0, p̄]`. -/
noncomputable def optPrice (Prof : ℝ → ℝ → ℝ) (α β pbar r : ℝ) : ℝ :=
  sSup {p | p ∈ Set.Icc (0 : ℝ) pbar ∧
    ∀ p' ∈ Set.Icc (0 : ℝ) pbar, bellmanObj Prof α β pbar p' r ≤ bellmanObj Prof α β pbar p r}

/-- The optimal reference price policy `q*(r) = α r + (1 − α) p*(r)`, p. 417. -/
noncomputable def optRef (Prof : ℝ → ℝ → ℝ) (α β pbar r : ℝ) : ℝ :=
  α * r + (1 - α) * optPrice Prof α β pbar r

/-- The optimal state path `{r*_t}` from `r₀`, p. 417: `r*_0 = r₀`, `r*_{t+1} = q*(r*_t)`. -/
noncomputable def statePath (Prof : ℝ → ℝ → ℝ) (α β pbar r₀ : ℝ) : ℕ → ℝ
  | 0 => r₀
  | t + 1 => optRef Prof α β pbar (statePath Prof α β pbar r₀ t)

/-- The optimal pricing path `p*_t = p*(r*_t)`, p. 417. -/
noncomputable def pricePath (Prof : ℝ → ℝ → ℝ) (α β pbar r₀ : ℝ) (t : ℕ) : ℝ :=
  optPrice Prof α β pbar (statePath Prof α β pbar r₀ t)

/-- A steady state `p**`, p. 417: `p*(p**) = q*(p**) = p**` (with `p** ∈ P`; `q*(p**) = p**`
follows from `p*(p**) = p**`). -/
def IsSteadyState (Prof : ℝ → ℝ → ℝ) (α β pbar r : ℝ) : Prop :=
  r ∈ Set.Icc (0 : ℝ) pbar ∧ optPrice Prof α β pbar r = r

end RobustBooking.Shared


