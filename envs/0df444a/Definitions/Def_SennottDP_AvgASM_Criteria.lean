-- Prove2me | Definitions.Def_SennottDP_AvgASM_Criteria
-- name    : SennottDP_AvgASM_Criteria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T09:12:06.145564+00:00
-- url     : https://prove2.me/theorems/0087412a-5d12-4a7e-815f-c0bb5a231833
-- title:
--   Finite horizon, discounted and average cost criteria and value functions (Sennott §2.4)
-- statement:
--   Let $\Delta$ be an MDC and $\theta$ a general policy. With zero terminal cost and no discounting, the **$n$-horizon expected cost** and **value function** are
--   $$v_{\theta,n}(i)=\sum_{t=0}^{n-1}E_\theta[C(X_t,A_t)\mid X_0=i],\qquad v_n(i)=\inf_\theta v_{\theta,n}(i).$$
--   For $\alpha\in(0,1)$ the **expected discounted cost** and the **discounted value function** are
--   $$V_{\theta,\alpha}(i)=\sum_{t\ge0}\alpha^t E_\theta[C(X_t,A_t)\mid X_0=i],\qquad V_\alpha(i)=\inf_\theta V_{\theta,\alpha}(i).$$
--   The **average cost** of $\theta$ and the **minimum average cost** are
--   $$J_\theta(i)=\limsup_{n\to\infty}\frac{v_{\theta,n}(i)}{n},\qquad J(i)=\inf_\theta J_\theta(i),$$
--   and $\theta$ is **average cost optimal** if $J_\theta(i)=J(i)$ for every $i\in S$. All infima are over the class of general (history-dependent, randomized) policies, and all quantities take values in $[0,\infty]$.
--
--   These are the criteria in which the chapter's approximation results are stated.
--
--   **Formalization Note** Values are in `ℝ≥0∞`; the discount factor is a real number entering through `ENNReal.ofReal`, and is only used for $\alpha\in(0,1)$. At $n=0$ the ratio $v_{\theta,0}/0$ is $0$, which does not affect the limit supremum.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 25–27, (2.11)–(2.16) and Definition 2.4.5

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Model

namespace SennottDP.AvgASM

open scoped ENNReal NNReal
open Filter

variable {S : Type*} {Act : Type*} [Countable S]

/-- The `n`-horizon expected cost with terminal cost `0` and no discounting,
`v_{θ,n}(i) = ∑_{t=0}^{n-1} E_θ[C(X_t,A_t) | X_0 = i]` ((2.11) with `α = 1`, `F = 0`), in `[0, ∞]`. -/
noncomputable def horizonCost {M : MDC S Act} (θ : Policy M) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range n, expCost θ i t

/-- The `n`-horizon value function `v_n(i) = inf_θ v_{θ,n}(i)` over all general policies
(terminal cost `0`, `α = 1`; (2.12), p. 26). -/
noncomputable def horizonValue (M : MDC S Act) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, horizonCost θ n i

/-- The expected discounted cost `V_{θ,α}(i) = ∑_{t ≥ 0} α^t E_θ[C(X_t,A_t) | X_0 = i]` (2.13),
p. 26, valued in `[0, ∞]` (used for `α ∈ (0, 1)`). -/
noncomputable def discCost {M : MDC S Act} (θ : Policy M) (α : ℝ) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ENNReal.ofReal α ^ t * expCost θ i t

/-- The discounted value function `V_α(i) = inf_θ V_{θ,α}(i)` over all general policies (2.14),
p. 26. -/
noncomputable def discValue (M : MDC S Act) (α : ℝ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, discCost θ α i

/-- The long-run expected average cost `J_θ(i) = limsup_{n→∞} v_{θ,n}(i)/n` (2.15), p. 27,
in `[0, ∞]`. -/
noncomputable def avgCost {M : MDC S Act} (θ : Policy M) (i : S) : ℝ≥0∞ :=
  limsup (fun n : ℕ => horizonCost θ n i / (n : ℝ≥0∞)) atTop

/-- The minimum average cost `J(i) = inf_θ J_θ(i)` over all general policies (2.16), p. 27. -/
noncomputable def avgValue (M : MDC S Act) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, avgCost θ i

/-- Definition 2.4.5: `θ` is average cost optimal if `J_θ(i) = J(i)` for all `i`. -/
def IsAverageOptimal {M : MDC S Act} (θ : Policy M) : Prop :=
  ∀ i, avgCost θ i = avgValue M i

end SennottDP.AvgASM


