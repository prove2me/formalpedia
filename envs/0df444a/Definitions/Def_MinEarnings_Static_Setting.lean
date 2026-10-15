-- Prove2me | Definitions.Def_MinEarnings_Static_Setting
-- name    : MinEarnings_Static_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:39:51.126273+00:00
-- url     : https://prove2.me/theorems/e3a27cfe-90f9-41f5-9700-770c5dcb8fb1
-- title:
--   §3, p. 8 and Definition 4 — the regulated ride-hailing marketplace: Q (1), utilization (2), equilibrium (3), profit (4), rule (5), stability (Definitions 1–2), static stability (8)
-- statement:
--   A ride-hailing platform sets, in each period $t$, a price $p_t \ge 0$ (charged to riders per hour of driving) and a wage $w_t \ge 0$ (paid to drivers per hour of driving riders). Demand $D(\cdot)$ and supply $S(\cdot)$ are fixed functions; $z_t$ denotes the drivers' expected hourly earnings. The file fixes the following objects.
--
--   1. **Regularity assumptions** (p. 8), on $[0,\infty)$: $D$ is positive, strictly decreasing and continuous; $S$ is strictly increasing, continuous, positive on $(0,\infty)$ and differentiable on $(0,\infty)$.
--   2. **Quantity, utilization and profit** ((1), (2), (4)):
--   $$Q(p,z)=\min\{D(p),S(z)\},\qquad u(p,z)=\frac{Q(p,z)}{S(z)},\qquad \pi(p,w,z)=(p-w)\,Q(p,z).$$
--   3. **Feasible policy**: $p_t\ge 0$ and $w_t\ge 0$ for all $t$.
--   4. **Equilibrium-augmented policy** (3): $z_t = w_t\, u(p_t,z_t)$ for all $t$, with $z_t>0$.
--   5. **Minimum earnings rule** (5): $w_{t+1} \ge M/u(p_t,z_t)$ for all $t$.
--   6. **Stability** (Definitions 1–2): the $M$-minimum-earnings marketplace is *stable* if some feasible equilibrium-augmented policy obeying (5) has a bounded wage sequence and $\pi(p_t,w_t,z_t)\ge 0$ for all but finitely many $t$.
--   7. **Static stability** (Definition 4): there are $p,w,z\ge 0$ and $u\in(0,1]$ with
--   $$u=\frac{Q(p,z)}{S(z)},\qquad z=w\,u,\qquad w\ge \frac{M}{u},\qquad p\ge w. \tag{8}$$
--
--   These are the objects of Theorem 3, which states that the two notions of stability coincide.
--
--   **Formalization Note** Time is 0-based: Lean's period $t$ is the paper's period $t+1$, and the rule (5) constrains every wage except the first. The equilibrium condition carries $z_t>0$: Lean evaluates $u(p,0)=Q/S(0)$ as $0$ when $S(0)=0$ (allowed by the assumptions), which would turn rule (5) into $M/0 = 0 \le w_{t+1}$ and make every $M$ stable; the paper's model has $z_t>0$ implicitly, since its rule divides by $u_t$. "Differentiable" is read as continuity on $[0,\infty)$ plus differentiability on $(0,\infty)$. "Bounded" is an upper bound $\exists B\ \forall t,\ w_t\le B$ (wages are non-negative), and "for all but finitely many $t$" is an eventually-along-`atTop` statement. The unimodality of $R(p)=pD(p)$ and the crossing point $w^*$ (p. 8) are not part of this file, because Theorem 3 does not use them.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), pp. 6–8, (1)–(5), Definitions 1–2, Regularity assumptions; p. 15, Definition 4, (8)

import Mathlib
import Definitions.Def_MinEarnings_Threshold_Setting

namespace MinEarnings.Static

/-- Static stability (Definition 4, system (8)): there are `p, w, z ≥ 0` and `u ∈ (0, 1]` with
`u = Q(p, z)/S(z)`, `z = w · u`, `w ≥ M/u` and `p ≥ w`. -/
def IsStaticallyStable (D S : ℝ → ℝ) (M : ℝ) : Prop :=
  ∃ p w z u : ℝ, 0 ≤ p ∧ 0 ≤ w ∧ 0 ≤ z ∧ 0 < u ∧ u ≤ 1 ∧
    u = MinEarnings.Threshold.util D S p z ∧ z = w * u ∧ M / u ≤ w ∧ w ≤ p

end MinEarnings.Static


