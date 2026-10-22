-- Prove2me | Definitions.Def_ReferencePricing_Myopic_value
-- name    : ReferencePricing_Myopic_value
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T09:23:21.295973+00:00
-- url     : https://prove2.me/theorems/05afa8bf-6430-4d3c-ae47-98d25c101935
-- title:
--   Value function V(r₀) of the infinite-horizon reference-price pricing problem and the Bellman objective W(p, r)
-- statement:
--   For a per-period profit $\Pi(p, r)$, memory $\alpha$, discount factor $\beta$ and price set $P = [0, \bar p]$, the **value function** is
--   $$V(r_0) = \sup_{(p_t) \subset P} \sum_{t=0}^{\infty} \beta^t\, \Pi(p_t, r_t), \qquad r_{t+1} = \alpha r_t + (1 - \alpha) p_t,$$
--   the supremum being over all price sequences with values in $P$. The **Bellman objective** of equation (2) is
--   $$W(p, r) = \Pi(p, r) + \beta\, V(\alpha r + (1 - \alpha) p).$$
--
--   $V$ is the firm's optimal long-run discounted profit from an initial reference price $r_0$, and $W(p,r)$ is the profit of charging $p$ today and acting optimally afterwards.
--
--   **Formalization Note.** $V$ is defined directly as a supremum over the (nonempty) type of sequences $\mathbb{N} \to [0, \bar p]$, not as a solution of the Bellman equation. Lean's real `⨆` and `∑'` return $0$ on an unbounded family or a non-summable series; under Assumption 1, $r_0 \in P$ and $0 < \beta < 1$ the path stays in $P$, per-period profit is bounded, every series is summable and the family is bounded, so these defaults are not reached on the domain the theorems use.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 417, Section 3, the sequence problem and Eq. (2)

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Model

namespace ReferencePricing.Myopic

/-- The value function of the pricing problem (p. 417): the supremum, over all price sequences
`p_t ∈ P = [0, p̄]`, of the discounted profit `∑_{t ≥ 0} β^t Π(p_t, r_t)` along the reference path
`r_{t+1} = α r_t + (1 - α) p_t` started at `r₀`. Generic in the per-period profit `Π`. -/
noncomputable def value (prof : ℝ → ℝ → ℝ) (α β pbar r₀ : ℝ) : ℝ :=
  ⨆ p : ℕ → Set.Icc (0 : ℝ) pbar,
    ∑' t, β ^ t * prof (p t) (refPath α r₀ (fun s => (p s : ℝ)) t)

/-- The Bellman objective (2), p. 417: `W(p, r) = Π(p, r) + β V(α r + (1 - α) p)`. -/
noncomputable def bellmanObjective (prof : ℝ → ℝ → ℝ) (α β pbar p r : ℝ) : ℝ :=
  prof p r + β * value prof α β pbar (α * r + (1 - α) * p)

end ReferencePricing.Myopic


