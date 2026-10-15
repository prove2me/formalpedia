-- Prove2me | Definitions.Def_MinEarnings_Shock_Setting
-- name    : MinEarnings_Shock_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:39:51.408011+00:00
-- url     : https://prove2.me/theorems/f2524baa-0ab8-47ee-9184-db56140aa8c5
-- title:
--   §3, p. 8 and §4.1 — the regulated ride-hailing marketplace: Q (1), utilization (2), equilibrium (3), profit (4), the rule (5), regularity assumptions, shock absorption (Definition 3)
-- statement:
--   A ride-hailing platform sets, in each period $t$, a price $p_t \ge 0$ per ride hour and a wage $w_t \ge 0$ per ride hour paid to drivers. It faces a demand curve $D(p)$ (ride hours demanded at price $p$) and a supply curve $S(z)$ (driver hours offered at hourly earnings $z$).
--
--   1. **Regularity assumptions.** $D$ is positive, strictly decreasing and continuous on $[0,\infty)$; $S$ is strictly increasing and continuous on $[0,\infty)$, and positive and differentiable on $(0,\infty)$.
--   2. **Revenue and cost.** $R(p) = p\,D(p)$ and $C(z) = z\,S(z)$.
--   3. **Standing assumptions.** $R$ is unimodal with its maximum at $p^* \ge 0$: strictly increasing on $[0,p^*]$ and strictly decreasing on $[p^*,\infty)$. Demand and supply cross at $w^* \ge 0$: $D(w^*) = S(w^*)$.
--   4. **Inverse cost.** A function $H$ is an inverse of $C$ on $(0,\infty)$ if $H(x) > 0$ and $C(H(x)) = x$ for every $x > 0$.
--   5. **Quantity, utilization, profit.**
--   $$Q(p,z) = \min\{D(p), S(z)\}, \qquad u(p,z) = \frac{Q(p,z)}{S(z)}, \qquad \pi(p,w,z) = (p-w)\,Q(p,z).$$
--   6. **Policies.** A policy $(p_t, w_t)_t$ is feasible if $p_t \ge 0$ and $w_t \ge 0$ for all $t$. Together with an earnings sequence $(z_t)_t$ it is equilibrium-augmented if $z_t > 0$ and $z_t = w_t\, u(p_t, z_t)$ for all $t$.
--   7. **Minimum earnings rule.** For a target $M$, $w_{t+1} \ge M/u(p_t, z_t)$ for every period $t$.
--   8. **Shock absorption (Definition 3).** An $M$-minimum-earnings marketplace absorbs a $u_0$ utilization shock if some feasible equilibrium-augmented policy satisfying the minimum earnings rule has a first wage $w_1 \ge M/u_0$, bounded wages, and $\pi(p_t, w_t, z_t) \ge 0$ in every period.
--
--   These are the objects of Theorem 2: a one-time drop of utilization to $u_0$ forces the next wage up to $M/u_0$, and the question is whether an unsubsidized platform (profit never negative) can keep wages bounded afterwards.
--
--   **Formalization Note** Time is 0-based: Lean's period $0$ is the paper's period $1$, so the shock constraint $w_1 \ge M/u_0$ is a condition on the first wage, and the rule constrains every later wage. The equilibrium condition requires $z_t > 0$: without it, $z_t = 0$ with $S(0) = 0$ would give the junk utilization $0/0 = 0$ in Lean and make the rule $M/0 = 0 \le w_{t+1}$ vacuous. "Differentiable" is read as differentiability on $(0,\infty)$ plus continuity on $[0,\infty)$, a weakening of the page. "$R$ is unimodal with a unique maximum at $p^*$" is read as strict increase on $[0,p^*]$ and strict decrease on $[p^*,\infty)$. $p^*$, $w^*$ and $H$ are parameters carrying their defining properties.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), pp. 6–8, (1)–(5), Regularity assumptions; p. 9, Lemma 1 (H); p. 13, Definition 3

import Mathlib
import Definitions.Def_MinEarnings_Threshold_Setting

namespace MinEarnings.Shock

/-- Definition 3 (p. 13): an `M`-minimum-earnings marketplace absorbs a `u₀` utilization shock if
some feasible equilibrium-augmented policy satisfying rule (5) has first wage at least `M / u₀`,
bounded wages and non-negative profit in every period. Lean's period `0` is the paper's period 1. -/
def AbsorbsShock (D S : ℝ → ℝ) (M u₀ : ℝ) : Prop :=
  ∃ p w z : ℕ → ℝ, MinEarnings.Threshold.IsFeasible p w ∧ MinEarnings.Threshold.IsEquilibrium D S p w z ∧ MinEarnings.Threshold.MinEarningsRule D S M p w z ∧
    M / u₀ ≤ w 0 ∧ (∃ B, ∀ t, w t ≤ B) ∧ ∀ t, 0 ≤ MinEarnings.Threshold.profit D S (p t) (w t) (z t)

end MinEarnings.Shock


