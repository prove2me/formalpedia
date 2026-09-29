-- Prove2me | Definitions.Def_LiuVanRyzin_Model
-- name    : LiuVanRyzin_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:35:25.14363+00:00
-- url     : https://prove2.me/theorems/86a04d28-ab6d-473b-ae46-d193f647e5cc
-- title:
--   Customer utility, early-purchase rule and purchase threshold $v(q)$
-- statement:
--   This module fixes the customer side of the two-period model of Liu and van Ryzin (2008), §2.
--
--   A monopolist sells a good at a preannounced price $p_1$ in period 1 and a lower price $p_2 < p_1$ in period 2. Period-2 requests are filled with probability $q$ (the **fill rate**), which customers anticipate correctly. Customers share a **utility function** $u:\mathbb R\to\mathbb R$ that is strictly increasing and concave, twice differentiable, and satisfies $u(0)=0$.
--
--   1. **Utility.** $u$ is an admissible customer utility when $u$ is strictly increasing, concave and continuous on $[0,\infty)$, differentiable with a differentiable derivative at every $x>0$, and $u(0)=0$.
--   2. **Buy rule** (§2.1). A customer with valuation $v$ buys in period 1 if and only if
--   $$v - p_1 \ge 0 \quad\text{and}\quad u(v-p_1) \ge q\,u(v-p_2).$$
--   3. **Threshold.** The purchase threshold is the infimum of the valuations that buy early,
--   $$v(q) = \inf\{v : v\ge p_1,\ u(v-p_1)\ge q\,u(v-p_2)\}.$$
--
--   For $q\in[0,1)$ the set in 3 is nonempty and bounded below by $p_1$ (Proposition 1), so the infimum is a genuine threshold; at $q=0$ it equals $p_1$, the paper's $v(0)=p_1$.
--
--   **Formalization Note** Monotonicity, concavity and continuity are imposed on $[0,\infty)$ and differentiability on $(0,\infty)$, because customers evaluate $u$ only at nonnegative arguments and the paper's own power utility $x^\gamma$ ($0<\gamma<1$) is not differentiable at $0$. Continuity at $0$ is not stated in the paper; it is implied by its "twice differentiable" for any utility differentiable at $0$, and holds for $x^\gamma$. Outside $q\in[0,1)$ the infimum is Lean's `sInf`, which is $0$ on an empty or unbounded-below set; no statement of the mission uses it there.
-- source:
--   Liu, van Ryzin, Strategic Capacity Rationing to Induce Early Purchases, Management Science 54(6):1115–1131 (2008), pp. 1120–1121, §2 and §2.1, buy rule and Eq. (2)

import Mathlib

namespace LiuVanRyzin

/-- The customer utility of Liu–van Ryzin (2008), §2, p. 1120: time invariant, strictly
increasing and concave, twice differentiable, with `u 0 = 0`. Customers only evaluate `u` at
nonnegative arguments, so monotonicity, concavity and continuity are imposed on `[0, ∞)` and
twice differentiability on `(0, ∞)` (the paper's own power utility `x ^ γ`, `0 < γ < 1`, is not
differentiable at `0`). Continuity at `0` is implied by the paper's "twice differentiable" for
every utility it differentiates at `0`, and is satisfied by `x ^ γ`. -/
def IsCustomerUtility (u : ℝ → ℝ) : Prop :=
  StrictMonoOn u (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) u ∧ ContinuousOn u (Set.Ici 0) ∧
    (∀ x : ℝ, 0 < x → DifferentiableAt ℝ u x ∧ DifferentiableAt ℝ (deriv u) x) ∧ u 0 = 0

/-- The buy rule of §2.1, p. 1120: facing prices `p₁` (period 1) and `p₂` (period 2) and
anticipated fill rate `q`, a customer with valuation `v` buys in period 1 if and only if
`u (v - p₁) ≥ q * u (v - p₂)` and `v - p₁ ≥ 0`. -/
def buysEarly (u : ℝ → ℝ) (p₁ p₂ q v : ℝ) : Prop :=
  p₁ ≤ v ∧ q * u (v - p₂) ≤ u (v - p₁)

/-- The threshold valuation `v(q)` of §2.1 (Proposition 1, Eq. (2)): the infimum of the
valuations that buy in period 1. Proposition 1 shows that for `q ∈ [0, 1)` the set is nonempty
and bounded below by `p₁`, so this infimum is the paper's cutoff. -/
noncomputable def cutoff (u : ℝ → ℝ) (p₁ p₂ q : ℝ) : ℝ :=
  sInf {v : ℝ | buysEarly u p₁ p₂ q v}

end LiuVanRyzin


