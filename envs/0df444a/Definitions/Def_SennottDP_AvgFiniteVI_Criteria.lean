-- Prove2me | Definitions.Def_SennottDP_AvgFiniteVI_Criteria
-- name    : SennottDP_AvgFiniteVI_Criteria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T09:02:57.915856+00:00
-- url     : https://prove2.me/theorems/c65b8d7a-7396-4a73-9cd0-3ff56ff5fae2
-- title:
--   Discounted cost, finite horizon cost and average cost criteria with their value functions
-- statement:
--   For a policy $\theta$, initial state $i$ and horizon $n$:
--
--   1. the **expected discounted cost** $V_{\theta,\alpha}(i) = \sum_{t \ge 0} \alpha^t E_\theta[C(X_t,A_t) \mid X_0 = i]$ and the **discounted value function** $V_\alpha(i) = \inf_\theta V_{\theta,\alpha}(i)$;
--   2. the **$n$-horizon expected cost** with terminal cost $0$, $v_{\theta,n}(i) = \sum_{t=0}^{n-1} E_\theta[C(X_t,A_t) \mid X_0 = i]$, and the **minimum $n$-horizon expected cost** $v_n(i) = \inf_\theta v_{\theta,n}(i)$;
--   3. the **average cost** $J_\theta(i) = \limsup_{n\to\infty} v_{\theta,n}(i)/n$, its lim inf version $J^*_\theta(i)$, and the **minimum average cost** $J(i) = \inf_\theta J_\theta(i)$.
--
--   A policy is **$\alpha$ discount optimal** if $V_{\theta,\alpha} = V_\alpha$ and **average cost optimal** if $J_\theta = J$. All infima range over all general policies.
--
--   **Formalization Note** All values are in $[0,\infty]$ (`ℝ≥0∞`). The theorems of this mission assume a finite state space, where every value is finite and is converted to `ℝ` with `toReal`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 26–27, Eqs. (2.11), (2.13)–(2.16), Definitions 2.4.4–2.4.5; Chapter 3, Eq. (3.2)

import Mathlib
import Definitions.Def_SennottDP_AvgFiniteVI_Model

namespace SennottDP.AvgFiniteVI

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

/-- The minimum `n`-horizon expected cost with terminal cost `0` (Chapter 3, with `α = 1`),
`v_n(i) = inf_θ v_{θ,n}(i)` over all general policies, valued in `[0, ∞]`. -/
noncomputable def horizonValue (M : MDC S Act) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, horizonCost θ n i

/-- Definition 2.4.4: `θ` is optimal for the `α`-discounted criterion if `V_{θ,α}(i) = V_α(i)`
for all `i`. -/
def IsDiscountOptimal {M : MDC S Act} (θ : Policy M) (α : ℝ) : Prop :=
  ∀ i, discCost θ α i = discValue M α i

/-- Definition 2.4.5: `θ` is average cost optimal if `J_θ(i) = J(i)` for all `i`. -/
def IsAverageOptimal {M : MDC S Act} (θ : Policy M) : Prop :=
  ∀ i, avgCost θ i = avgValue M i

end SennottDP.AvgFiniteVI


