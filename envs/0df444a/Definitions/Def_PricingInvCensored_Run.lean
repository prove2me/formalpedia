-- Prove2me | Definitions.Def_PricingInvCensored_Run
-- name    : PricingInvCensored_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:00.354401+00:00
-- url     : https://prove2.me/theorems/ca4ecc17-618f-45b9-92f5-8e4352acb3d1
-- title:
--   The run of Algorithm 3 on the lost-sales system with censored feedback, the parameters $C_1,C_2$ of Theorem 1, and the regret
-- statement:
--   **The run and the regret** (§2.1 pp. 4–6, Theorem 1 p. 19). Fix an instance, parameters, an initial stock $x_1$ and a noise sequence $(\varepsilon_t)$ on a probability space. At period $t$ the controller sees $x_t$ and returns a price $p_t$ and a target; the stock is raised to
--   $$y_t=\max(\text{target}_t,x_t),$$
--   demand $D_t=\lambda(p_t)+\varepsilon_t$ realizes, the firm observes the sales $o_t=\min\{D_t,y_t\}$, and $x_{t+1}=\max\{y_t-D_t,0\}$. The **regret** over $T$ periods is
--   $$\sum_{t=1}^{T}\big[Q(p^*,y^*)-Q(p_t,y_t)\big],$$
--   pathwise, drain periods included.
--
--   The module also defines Theorem 1's parameters
--   $$C_1=2(b+\overline p+h)\sqrt{\ln T},\qquad C_2'=2(\overline p+h)\bar y+6\overline p+b\bar y(K+1),\qquad C_2=\big[16C_2'C_1s^{-2}\kappa^{-1}(1+(b+h)^{-1})\ln T\big]^2,$$
--   the epoch width $\beta_\zeta-\alpha_\zeta=(\overline p-\underline p)(2/3)^\zeta/3$, and the condition that the printed algorithm is defined at every epoch: $x_\zeta+\lceil\log_2(x_\zeta\bar y)\rceil>0$ and $N_\zeta\ge1$ for $x_\zeta=C_2/(\beta_\zeta-\alpha_\zeta)^4$.
--
--   **Formalization Note** Periods are indexed from $0$. Nothing can be disposed of, so the level is the larger of the target and the stock. The controller receives only $x_t$, the realized level and the sales. The run continues past $T$, but the regret sums the first $T$ periods.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), §2.1 pp.4–6, Algorithm 3 p.18, Theorem 1 p.19

import Mathlib
import Definitions.Def_PricingInvCensored_Model
import Definitions.Def_PricingInvCensored_Controller

open MeasureTheory

namespace PricingInvCensored

/-- `C₁ = 2(b + p̄ + h)√(ln T)`, Theorem 1, p.19 (Chen, Wang & Zhou, SSRN 3750413). -/
noncomputable def C1 (I : Instance) (T : ℕ) : ℝ :=
  2 * (I.market.b + I.market.high + I.market.h) * Real.sqrt (Real.log T)

/-- `C′₂ = 2(p̄ + h)ȳ + 6p̄ + bȳ(K + 1)`, Theorem 1, p.19 (defined in Lemma 2, p.17). -/
noncomputable def C2' (I : Instance) : ℝ :=
  2 * (I.market.high + I.market.h) * I.ybar + 6 * I.market.high + I.market.b * I.ybar * (I.K + 1)

/-- `C₂ = [16 C′₂ C₁ s⁻² κ⁻¹ (1 + (b + h)⁻¹) ln T]²`, Theorem 1, p.19 (the printed stray `)` is
dropped). -/
noncomputable def C2 (I : Instance) (T : ℕ) : ℝ :=
  (16 * C2' I * C1 I T * (I.s ^ 2)⁻¹ * I.kappa⁻¹ * (1 + (I.market.b + I.market.h)⁻¹) *
    Real.log T) ^ 2

/-- The parameters with which Theorem 1 (p.19) runs Algorithm 3 on instance `I` with horizon `T`. -/
noncomputable def params (I : Instance) (T : ℕ) : Params :=
  ⟨I.market.low, I.market.high, I.market.b, I.market.h, I.ybar, C1 I T, C2 I T⟩

/-- The width `β_ζ − α_ζ = (p̄ − p̲)(2/3)^ζ / 3` of epoch `ζ` of Algorithm 3 (it does not depend on
the data: each trisection update keeps two thirds of the interval). -/
noncomputable def epochWidth (I : Instance) (ζ : ℕ) : ℝ :=
  (I.market.high - I.market.low) * (2 / 3) ^ ζ / 3

/-- **The printed algorithm is defined at every epoch**: for every `ζ`, with
`x_ζ = C₂/(β_ζ − α_ζ)⁴`, the inner logarithm argument of `g` is positive,
`x_ζ + ⌈log₂(x_ζ ȳ)⌉ > 0`, and the budget `N_ζ = ⌈g(x_ζ)⌉` is at least `1`.

**Formalization Note.** Otherwise `g` takes the logarithm of a nonpositive number, or Algorithms 1–2
divide by `n = 0`; such horizons are excluded, not reinterpreted. -/
def BudgetsDefined (I : Instance) (T : ℕ) : Prop :=
  ∀ ζ : ℕ,
    0 < C2 I T / epochWidth I ζ ^ 4 + ⌈Real.logb 2 (C2 I T / epochWidth I ζ ^ 4 * I.ybar)⌉ ∧
      1 ≤ budget (params I T) (epochWidth I ζ)

/-- **The run of Algorithm 3 on the lost-sales inventory system**, Chen, Wang & Zhou,
SSRN 3750413, §2.1 (pp.4–5) and Algorithms 1–3 (pp.13, 16, 18): the pair (starting stock `x_t`,
controller state) at period `t`.

At period `t` the controller sees `x_t` and returns a price `p_t` and a target; the stock is raised
to `y_t = max(target, x_t)`; demand is `D_t = λ(p_t) + ε_t`; the firm observes the sales
`o_t = min{D_t, y_t}`; and `x_{t+1} = max{y_t − D_t, 0}`.

**Formalization Note.** Periods are indexed `0, 1, …` (the paper's `t = 1, 2, …`), and `x₁` is the
stock at the first period. Nothing can be disposed of, so the stock level is `max(target, x_t)`.
The controller receives only `x_t`, the realized level and the sales `o_t`. -/
noncomputable def runState {Ω : Type*} (I : Instance) (P : Params) (x1 : ℝ)
    (ε : ℕ → Ω → ℝ) (ω : Ω) : ℕ → ℝ × State
  | 0 => (x1, initState P)
  | t + 1 =>
    let xs := runState I P x1 ε ω t
    let dec := step P xs.2 xs.1
    let y := max dec.1.2 xs.1
    let D := I.market.demand dec.1.1 + ε t ω
    (max (y - D) 0, update P dec.2 xs.1 y (min D y))

/-- The price `p_t` posted at period `t` of the run. -/
noncomputable def price {Ω : Type*} (I : Instance) (P : Params) (x1 : ℝ) (ε : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  (step P (runState I P x1 ε ω t).2 (runState I P x1 ε ω t).1).1.1

/-- The stock level `y_t = max(target_t, x_t)` after ordering at period `t` of the run. -/
noncomputable def level {Ω : Type*} (I : Instance) (P : Params) (x1 : ℝ) (ε : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  max (step P (runState I P x1 ε ω t).2 (runState I P x1 ε ω t).1).1.2 (runState I P x1 ε ω t).1

/-- **The regret** `Σ_{t=1}^T [Q(p*, y*) − Q(p_t, y_t)]` of the run over the first `T` periods
(Chen, Wang & Zhou, SSRN 3750413, p.6 and Theorem 1, p.19), pathwise (before expectation), drain
periods included. -/
noncomputable def regret {Ω : Type*} (I : Instance) (P : Params) (pStar yStar x1 : ℝ)
    (ε : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T,
    (I.market.Q pStar yStar - I.market.Q (price I P x1 ε t ω) (level I P x1 ε t ω))

end PricingInvCensored


