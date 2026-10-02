-- Prove2me | Definitions.Def_SennottDP_ResidualLife_MSDist
-- name    : SennottDP_ResidualLife_MSDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T10:09:41.659226+00:00
-- url     : https://prove2.me/theorems/9f417222-5f14-4bf1-a738-81c30632df55
-- title:
--   Distributions on {1,2,…}: tail F*, moments, residual life Y_s and bounded mean residual lifetimes (BMRL)
-- statement:
--   Let $Y$ be a random variable with values in $\{1,2,3,\dots\}$ and distribution $u_y = P(Y=y)$, $y \ge 1$. Only the law of $Y$ matters, so $Y$ is represented by the sequence $(u_y)_{y \ge 0}$ of nonnegative numbers with
--   $$\sum_{y \ge 0} u_y = 1, \qquad u_0 = 0.$$
--
--   1. The **complement of the cumulative distribution** is $F^*(y) = P(Y > y) = \sum_{w > y} u_w$ for $y \ge 0$; in particular $F^*(0) = 1$.
--   2. The **$k$-th moment** is $E[Y^k] = \sum_{y} y^k u_y \in [0,\infty]$; it may be infinite.
--   3. For $s \ge 0$ with $F^*(s) > 0$, the **residual life** $Y_s$ (the remaining service time given that the service has lasted $s$ slots and is not completed) has distribution
--   $$P(Y_s = y) = P(Y = s+y \mid Y > s) = \frac{u_{s+y}}{F^*(s)}, \qquad y \ge 1,$$
--   and $Y_0 = Y$. Its $k$-th moment is $E[Y_s^k] = \sum_y y^k P(Y_s = y) \in [0,\infty]$, and $E[Y_s]$ is the **mean residual lifetime**.
--   4. The distribution of $Y$ has **bounded mean residual lifetimes with bound $U$** (BMRL-$U$) if $U$ is a finite constant with
--   $$E[Y_s] \le U \quad \text{for every } s \ge 0 \text{ with } F^*(s) > 0,$$
--   and it is **BMRL** if it is BMRL-$U$ for some finite $U$.
--
--   These are the objects of Section 9.2, where a service-time (or lifetime) distribution is modelled slot by slot.
--
--   **Formalization Note** Probabilities and moments are `ℝ≥0∞`-valued `tsum`s, so an infinite moment is `⊤` and "finite" means `< ⊤`; no Bochner integral is used. $Y_s$ is defined by the book only when $F^*(s) > 0$; BMRL is therefore required exactly at those $s$ (for a bounded $Y$ with largest value $B$ the residual life is undefined for $s \ge B$, and every bounded distribution is BMRL). `U` is a nonnegative real (`ℝ≥0`), i.e. finite.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 202, Section 9.2 (u_y, F, F*); p. 203, Eq. (9.7) (residual life Y_s); p. 204, Definition 9.2.4 (BMRL)

import Mathlib

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), §9.2, p. 202: `u` is the distribution `u_y = P(Y = y)` of a random variable `Y`
taking values in `{1, 2, 3, …}`. It is encoded as a function on `ℕ` with total mass one and no mass
at `0`. -/
def IsDistOnPos (u : ℕ → ℝ≥0∞) : Prop :=
  ∑' y : ℕ, u y = 1 ∧ u 0 = 0

/-- Sennott (1999), §9.2, p. 202: the complement of the cumulative distribution,
`F*(y) = P(Y > y) = ∑_{w > y} u_w`, for `y ≥ 0` (so `F*(0) = 1` when `u` lives on `{1, 2, …}`). -/
noncomputable def tail (u : ℕ → ℝ≥0∞) (y : ℕ) : ℝ≥0∞ :=
  ∑' w : ℕ, if y < w then u w else 0

/-- The `k`-th moment `E[Y^k] = ∑_y y^k u_y ∈ [0, ∞]` of a distribution `u` on `ℕ`
(possibly `+∞`). -/
noncomputable def moment (u : ℕ → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ∑' y : ℕ, (y : ℝ≥0∞) ^ k * u y

/-- Sennott (1999), (9.7), p. 203: the distribution of the residual life `Y_s` after `s` completed
slots, `P(Y_s = y) = P(Y = s + y | Y > s) = u_{s+y} / F*(s)` for `y ≥ 1`, and `0` at `y = 0`.
It is meaningful when `F*(s) > 0`; every statement below only uses it under that condition. -/
noncomputable def residualDist (u : ℕ → ℝ≥0∞) (s : ℕ) (y : ℕ) : ℝ≥0∞ :=
  if 1 ≤ y then u (s + y) / tail u s else 0

/-- The `k`-th moment `E[Y_s^k]` of the residual life `Y_s` (in `[0, ∞]`); `k = 1` gives the mean
residual lifetime `E[Y_s]`. -/
noncomputable def residualMoment (u : ℕ → ℝ≥0∞) (s k : ℕ) : ℝ≥0∞ :=
  moment (residualDist u s) k

/-- Sennott (1999), Definition 9.2.4, p. 204: the distribution `u` has bounded mean residual
lifetimes with bound `U` (BMRL-`U`): `E[Y_s] ≤ U` for every `s ≥ 0` at which the residual life is
defined, i.e. `F*(s) = P(Y > s) > 0`. -/
def IsBMRL (u : ℕ → ℝ≥0∞) (U : ℝ≥0) : Prop :=
  ∀ s : ℕ, 0 < tail u s → residualMoment u s 1 ≤ (U : ℝ≥0∞)

/-- Sennott (1999), Definition 9.2.4, p. 204: the distribution `u` is BMRL, i.e. BMRL-`U` for some
finite constant `U`. -/
def IsBMRLDist (u : ℕ → ℝ≥0∞) : Prop :=
  ∃ U : ℝ≥0, IsBMRL u U

end SennottDP.ResidualLife


