-- Prove2me | Definitions.Def_SennottDP_AvgFinite_Criteria
-- name    : SennottDP_AvgFinite_Criteria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T08:05:41.233698+00:00
-- url     : https://prove2.me/theorems/5b59732c-7376-42ce-8a51-2e53e2a2c139
-- title:
--   Discounted cost $V_{\theta,\alpha}$, average costs $J_\theta$, $J^*_\theta$, and the value functions $V_\alpha$, $J$
-- statement:
--   Let $\Delta$ be an MDC and $\theta$ a policy; write $u_t = E_\theta[C(X_t,A_t) \mid X_0 = i]$.
--
--   1. The **expected discounted cost** with discount factor $\alpha$ is
--   $$V_{\theta,\alpha}(i) = \sum_{t=0}^{\infty} \alpha^t\, E_\theta[C(X_t,A_t) \mid X_0 = i] \in [0,\infty].$$
--   The book's criterion uses $0 < \alpha < 1$; as in (4.24) the same power series is considered for every $\alpha \in [0,\infty)$.
--   2. The **$n$ horizon expected cost** (terminal cost $0$) is $v_{\theta,n}(i) = \sum_{t=0}^{n-1} E_\theta[C(X_t,A_t) \mid X_0 = i]$.
--   3. The **long-run expected average cost** is
--   $$J_\theta(i) = \limsup_{n\to\infty} \frac{v_{\theta,n}(i)}{n},$$
--   and $J^*_\theta(i)$ is the same expression with $\liminf$ in place of $\limsup$.
--   4. The **discounted value function** and the **minimum average cost** are
--   $$V_\alpha(i) = \inf_\theta V_{\theta,\alpha}(i), \qquad J(i) = \inf_\theta J_\theta(i), \qquad J^*(i) = \inf_\theta J^*_\theta(i),$$
--   the infima being taken over **all** policies.
--   5. A policy $\theta$ is **$\alpha$ discount optimal** if $V_{\theta,\alpha}(i) = V_\alpha(i)$ for every $i$, and **average cost optimal** if $J_\theta(i) = J(i)$ for every $i$.
--
--   All these quantities may equal $+\infty$ (Remark 2.4.2).
--
--   **Formalization Note** Every quantity is valued in `ℝ≥0∞`, so `+∞` is represented and no infimum or sum takes a junk value. The real discount factor enters as `ENNReal.ofReal α`. `v_{θ,n}/n` is computed in `ℝ≥0∞`; at `n = 0` it is `0`, which does not affect the $\limsup$/$\liminf$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 25–27, Eqs. (2.11), (2.13)–(2.16), Definitions 2.4.4–2.4.5; p. 70, Eq. (4.24)

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal
open Filter

variable {S : Type*} {Act : Type*} [Countable S]

/-- The expected discounted cost `V_{θ,α}(i) = ∑_{t ≥ 0} α^t E_θ[C(X_t,A_t) | X_0 = i]` (2.13),
p. 26, valued in `[0, ∞]`. As in (4.24), p. 70, the power series is defined for every `α ≥ 0`
(the real `α` enters through `ENNReal.ofReal`); the book's criterion uses `α ∈ (0,1)`. -/
noncomputable def discCost {M : MDC S Act} (θ : Policy M) (α : ℝ) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ENNReal.ofReal α ^ t * expCost θ i t

/-- The `n`-horizon expected (undiscounted) cost with terminal cost `0`,
`v_{θ,n}(i) = ∑_{t=0}^{n-1} E_θ[C(X_t,A_t) | X_0 = i]` ((2.11) with `F = 0`), valued in `[0, ∞]`. -/
noncomputable def horizonCost {M : MDC S Act} (θ : Policy M) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range n, expCost θ i t

/-- The long-run expected average cost `J_θ(i) = limsup_{n→∞} v_{θ,n}(i)/n` (2.15), p. 27,
in `[0, ∞]`. -/
noncomputable def avgCost {M : MDC S Act} (θ : Policy M) (i : S) : ℝ≥0∞ :=
  limsup (fun n : ℕ => horizonCost θ n i / (n : ℝ≥0∞)) atTop

/-- `J*_θ(i)`: (2.15) with the limit supremum replaced by the limit infimum, p. 27. -/
noncomputable def avgCostLiminf {M : MDC S Act} (θ : Policy M) (i : S) : ℝ≥0∞ :=
  liminf (fun n : ℕ => horizonCost θ n i / (n : ℝ≥0∞)) atTop

/-- The discounted value function `V_α(i) = inf_θ V_{θ,α}(i)` over all general policies (2.14),
p. 26. -/
noncomputable def discValue (M : MDC S Act) (α : ℝ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, discCost θ α i

/-- The minimum average cost `J(i) = inf_θ J_θ(i)` over all general policies (2.16), p. 27. -/
noncomputable def avgValue (M : MDC S Act) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, avgCost θ i

/-- `J*(i) = inf_θ J*_θ(i)`, p. 27. -/
noncomputable def avgValueLiminf (M : MDC S Act) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, avgCostLiminf θ i

/-- Definition 2.4.4: `θ` is optimal for the `α`-discounted criterion if `V_{θ,α}(i) = V_α(i)`
for all `i`. -/
def IsDiscountOptimal {M : MDC S Act} (θ : Policy M) (α : ℝ) : Prop :=
  ∀ i, discCost θ α i = discValue M α i

/-- Definition 2.4.5: `θ` is average cost optimal if `J_θ(i) = J(i)` for all `i`. -/
def IsAverageOptimal {M : MDC S Act} (θ : Policy M) : Prop :=
  ∀ i, avgCost θ i = avgValue M i

end SennottDP.AvgFinite


