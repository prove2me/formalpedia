-- Prove2me | Definitions.Def_VeinottWagnerSS_RenewalCost_Supplement_InfiniteHorizon
-- name    : VeinottWagnerSS_RenewalCost_Supplement_InfiniteHorizon
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:25:36.817652+00:00
-- url     : https://prove2.me/theorems/4fa8489e-654e-4647-9eeb-c8244c2f3397
-- title:
--   Infinite-period model — stationary $(s, S)$ policy, discounted cost (3), average cost (4) and infinite-period optimality
-- statement:
--   These definitions extend the published $n$-period model of Veinott and Wagner (`VeinottWagnerSS.Bounds.Model`) to the infinite period model of pp. 529–530.
--
--   In that model the demands $\xi_1,\xi_2,\dots$ are i.i.d. with distribution $\varphi$ on $\{0,1,2,\dots\}$, $X_t$ is the stock on hand plus on order before ordering in period $t$, and a policy $Y$ chooses the level $Y_t\ge X_t$ after ordering as any function of the initial level $X_1=x$ and the past demands; $X_{t+1}=Y_t-\xi_t$. With set-up cost $K$, discount factor $\alpha$ and one-period cost $G_\alpha$, the reduced $n$-period cost of Eq. (2) is
--
--   $$
--   f_n(x\mid Y)=\sum_{t=1}^{n}\alpha^{t-1}\bigl[K\,E\,\delta(Y_t-X_t)+E\,G_\alpha(Y_t)\bigr],
--   $$
--
--   valued in $[-\infty,+\infty]$, where $\delta(z)=1$ for $z>0$ and $\delta(0)=0$.
--
--   1. **Stationary $(s,S)$ policy.** For integers $s,S$, the stationary $(s,S)$ policy uses in every period the rule $Y_t=S$ if $X_t<s$ and $Y_t=X_t$ if $X_t\ge s$.
--   2. **Discounted cost**, Eq. (3): for $0\le\alpha<1$,
--   $$
--   f(x\mid Y)=\lim_{n\to\infty}f_n(x\mid Y),
--   $$
--   which may be $+\infty$.
--   3. **Average cost**, Eq. (4): for $\alpha=1$,
--   $$
--   a_1(x\mid Y)=\liminf_{n\to\infty}\frac1n f_n(x\mid Y).
--   $$
--   4. **Optimality in the infinite period model.** A policy $Y^*$ is optimal if it is admissible and, for every initial level $x$ and every admissible policy $Y$, $f(x\mid Y^*)\le f(x\mid Y)$ when $\alpha<1$, and $a_1(x\mid Y^*)\le a_1(x\mid Y)$ when $\alpha=1$.
--
--   These are the objects in which Theorems 3 and 4(b) state that a particular stationary $(s,S)$ policy is optimal among all history-dependent policies.
--
--   **Formalization Note** The policy model, admissibility, the cost $f_n$ and the $(s,S)$ rule are the published `VeinottWagnerSS.Bounds.Model`; demand is a `PMF ℕ` and costs are `EReal`. The stationary policy is defined by the recursion $Y_1=\mathrm{rule}(x)$, $Y_{t+1}=\mathrm{rule}(Y_t-\xi_t)$. The limit in (3) is written as a `liminf`: it is the limit whenever the limit exists, which is the case for $0\le\alpha<1$, $K\ge0$ and $G_\alpha$ bounded below (each period's cost is bounded below by $\inf G_\alpha$, so the partial sums converge in $[-\infty,+\infty]$). The criterion `infCost` selects (3) for $\alpha<1$ and (4) otherwise; it is only used with $0\le\alpha\le1$.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), pp. 529–530, Eqs. (3) and (4) (infinite period model, optimality), p. 529 (stationary (s, S) policy), p. 529, Eq. (2) (n-period cost)

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model

namespace VeinottWagnerSS.RenewalCost.Supplement

open VeinottWagnerSS.Bounds
open scoped ENNReal

/-- The level `Y_{t+1}` reached after ordering in period `t + 1` when the stationary `(s, S)` rule
(p. 529: `Y = S` if `X < s`, `Y = X` if `X ≥ s`) is used in every period from `X₁ = x`, along the
demand history `h = (ξ₁, ⋯, ξ_t)`: `Y₁ = sSRule s S x` and
`Y_{t+1} = sSRule s S (Y_t − ξ_t)`. -/
def stationaryLevel (s S x : ℤ) : (t : ℕ) → (Fin t → ℕ) → ℤ
  | 0, _ => sSRule s S x
  | t + 1, h => sSRule s S (stationaryLevel s S x t (Fin.init h) - (h (Fin.last t) : ℤ))

/-- The stationary `(s, S)` policy (p. 529, "When `s_t = s` and `S_t = S` for all `t`, the
`(s, S)` policy is called stationary"), as a policy of the history-dependent model
`VeinottWagnerSS.Bounds.Policy`: in every period it uses the `(s, S)` rule. -/
def stationary (s S : ℤ) : Policy := fun t x h => stationaryLevel s S x t h

/-- The infinite-period discounted cost (3), p. 529: `f(x | Y) = lim_{n→∞} f_n(x | Y)`, "which
may be infinite", with `f_n(x | Y)` the reduced `n`-period cost of Eq. (2)
(`VeinottWagnerSS.Bounds.cost`), valued in the extended reals. It is written as the `liminf`
of the sequence `n ↦ f_n(x | Y)`, which is the limit whenever the limit exists (in particular
when `0 ≤ α < 1`, `K ≥ 0` and `G_α` is bounded below, where the sequence of partial sums
converges in `[−∞, +∞]`). -/
noncomputable def discountedCost (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (x : ℤ) (Y : Policy) :
    EReal :=
  Filter.liminf (fun n : ℕ => cost φ G K α n x Y) Filter.atTop

/-- The undiscounted (`α = 1`) average cost per period (4), p. 530:
`a₁(x | Y) = liminf_{n→∞} (1/n) f_n(x | Y)`, with `f_n(x | Y)` the reduced `n`-period cost of
Eq. (2) at `α = 1`, valued in the extended reals. -/
noncomputable def averageCost (φ : PMF ℕ) (G : ℤ → ℝ) (K : ℝ) (x : ℤ) (Y : Policy) : EReal :=
  Filter.liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * cost φ G K 1 n x Y) Filter.atTop

/-- The infinite-period criterion of p. 529–530: the discounted cost `f(x | Y)` of (3) when
`α < 1`, and the average cost `a₁(x | Y)` of (4) otherwise (it is used only for `α = 1`). -/
noncomputable def infCost (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (x : ℤ) (Y : Policy) : EReal :=
  if α < 1 then discountedCost φ G K α x Y else averageCost φ G K x Y

/-- `Y` is optimal for the infinite period model (pp. 529–530): it is admissible and its
infinite-period cost (`f(x | Y)` for `0 ≤ α < 1`, `a₁(x | Y)` for `α = 1`) is at most that of
every admissible (history-dependent) policy `Y'`, for every initial level `x`. -/
def IsInfOptimal (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (Y : Policy) : Prop :=
  Admissible Y ∧ ∀ Y' : Policy, Admissible Y' → ∀ x : ℤ, infCost φ G K α x Y ≤ infCost φ G K α x Y'

end VeinottWagnerSS.RenewalCost.Supplement


