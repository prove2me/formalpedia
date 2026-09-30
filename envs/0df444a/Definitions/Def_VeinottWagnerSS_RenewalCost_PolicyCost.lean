-- Prove2me | Definitions.Def_VeinottWagnerSS_RenewalCost_PolicyCost
-- name    : VeinottWagnerSS_RenewalCost_PolicyCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T12:58:58.30015+00:00
-- url     : https://prove2.me/theorems/155edddb-b9e6-4827-af64-12591e09217c
-- title:
--   Discounted cost $f(x \mid s, S)$ and cost per period $a_\alpha(x \mid s, S)$ of a stationary $(s, S)$ policy
-- statement:
--   Consider the reduced periodic-review inventory model of Veinott and Wagner (1965): in period $t$ the stock level before ordering is $X_t$, the stock level after ordering is $Y_t \ge X_t$, the cost of the period is $K\delta(Y_t - X_t) + G_\alpha(Y_t)$ with set-up cost $K$ and $\delta(0) = 0$, $\delta(z) = 1$ for $z > 0$, and $X_{t+1} = Y_t - \xi_t$, where the demands $\xi_t$ are i.i.d. with distribution $\varphi$.
--
--   Under the **stationary $(s, S)$ policy** with integers $s \le S$,
--   $$Y_t = \begin{cases} S & X_t < s, \\ X_t & X_t \ge s. \end{cases}$$
--   Started from $X_1 = x$, the law of $X_t$ is computed recursively: $\Pr(X_1 = x) = 1$ and
--   $$\Pr(X_{t+1} = z) = \sum_{y \in \mathbb Z} \Pr(X_t = y)\,\varphi\bigl(Y(y) - z\bigr),$$
--   where $Y(y)$ is the order-up-to level at stock $y$ and the term is $0$ when $z > Y(y)$. The **total expected discounted cost** of the policy is
--   $$f(x \mid s, S) = \sum_{t=1}^{\infty} \alpha^{t-1}\, E\bigl[K\delta(Y_t - X_t) + G_\alpha(Y_t)\bigr],$$
--   and the **equivalent cost per period** is $a_\alpha(x \mid s, S) = (1 - \alpha) f(x \mid s, S)$, so that $f = \sum_{i \ge 1} \alpha^{i-1} a_\alpha$.
--
--   This is the criterion whose closed form, Eq. (11) of the paper, is the goal of the mission; the $(s, S)$ policy is then chosen by minimizing $a_\alpha$.
--
--   **Formalization Note** The model is the paper's reduced model of Eq. (2): the unit purchase cost is set to $0$ and $L$ is replaced by $G_\alpha$, so the primitives are $G_\alpha : \mathbb Z \to \mathbb R$, $K$, $\alpha$ and $\varphi$. `stateDist D s S x t` is the law of $X_{t+1}$ and `expectedPeriodCost … t` the expectation for period $t+1$, discounted by $\alpha^t$. All sums are real `tsum`s. For $0 \le \alpha < 1$ they are summable for every $G_\alpha$, because after period $1$ the order-up-to level lies in the finite set $\{S\} \cup [s, \max(x, S)]$, so the per-period cost is bounded.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 527 (X_t, Y_t, δ, X_{t+1} = Y_t − ξ_t), p. 529 (Eq. (2), (3), stationary (s, S) rule), p. 533 (f(x | s, S)), p. 534 (a_α(x | s, S) = (1 − α) f(x | s, S))

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand

namespace VeinottWagnerSS.RenewalCost

/-- `δ(z)` of p. 527: `δ(0) = 0` and `δ(z) = 1` for `z > 0` (order quantities are
non-negative; the value `0` is also returned for `z < 0`, which never occurs below). -/
def delta (z : ℤ) : ℝ := if 0 < z then 1 else 0

/-- The stationary `(s, S)` ordering rule (p. 529): the stock level after ordering is
`Y = S` if `X < s` and `Y = X` if `X ≥ s`. -/
def sSOrder (s S x : ℤ) : ℤ := if x < s then S else x

/-- The law of the stock level `X_{t+1}` (before ordering, in period `t + 1`) when the stationary
`(s, S)` policy is followed from `X₁ = x`: `stateDist D s S x t z = Pr(X_{t+1} = z)`.
`X₁ = x` surely, and `X_{t+1} = Y_t − ξ_t` (p. 527) with `Y_t = sSOrder s S X_t` and `ξ_t`
independent of `X_t` with law `φ`, so
`Pr(X_{t+2} = z) = ∑_y Pr(X_{t+1} = y) · φ(sSOrder s S y − z)` (the term vanishing when
`z > sSOrder s S y`). -/
noncomputable def stateDist (D : DemandDist) (s S x : ℤ) : ℕ → ℤ → ℝ
  | 0 => fun z => if z = x then 1 else 0
  | t + 1 => fun z => ∑' y : ℤ, stateDist D s S x t y *
      (if z ≤ sSOrder s S y then D.φ (sSOrder s S y - z).toNat else 0)

/-- The reduced cost of a period whose starting stock is `y` under the `(s, S)` rule (p. 529,
(2)): `K δ(Y − X) + G_α(Y)` with `X = y`, `Y = sSOrder s S y`. -/
noncomputable def periodCost (K : ℝ) (G : ℤ → ℝ) (s S y : ℤ) : ℝ :=
  K * delta (sSOrder s S y - y) + G (sSOrder s S y)

/-- The expected cost of period `t + 1`, `E[K δ(Y_{t+1} − X_{t+1}) + G_α(Y_{t+1})]`, under the
stationary `(s, S)` policy from `X₁ = x`. -/
noncomputable def expectedPeriodCost (D : DemandDist) (K : ℝ) (G : ℤ → ℝ) (s S x : ℤ)
    (t : ℕ) : ℝ :=
  ∑' y : ℤ, stateDist D s S x t y * periodCost K G s S y

/-- `f(x | s, S)` (p. 533, with (2)–(3) of p. 529): the total expected discounted cost of the
stationary `(s, S)` policy started at `X₁ = x`,
`f(x | s, S) = ∑_{t=1}^{∞} α^{t−1} E[K δ(Y_t − X_t) + G_α(Y_t)]`
(period `t + 1` below carries the factor `α^t`). -/
noncomputable def fCost (D : DemandDist) (α K : ℝ) (G : ℤ → ℝ) (s S x : ℤ) : ℝ :=
  ∑' t : ℕ, α ^ t * expectedPeriodCost D K G s S x t

/-- The equivalent cost per period `a_α(x | s, S) = (1 − α) f(x | s, S)` (p. 534). -/
noncomputable def aCost (D : DemandDist) (α K : ℝ) (G : ℤ → ℝ) (s S x : ℤ) : ℝ :=
  (1 - α) * fCost D α K G s S x

end VeinottWagnerSS.RenewalCost


