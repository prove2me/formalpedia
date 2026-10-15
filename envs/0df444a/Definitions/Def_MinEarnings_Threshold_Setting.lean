-- Prove2me | Definitions.Def_MinEarnings_Threshold_Setting
-- name    : MinEarnings_Threshold_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:31.391589+00:00
-- url     : https://prove2.me/theorems/8b1be4b5-953a-45a3-9bb7-9697c59d1733
-- title:
--   §3–4, pp. 6–11 — the regulated ride-hailing marketplace: Q (1), utilization (2), equilibrium (3), profit (4), the rule (5), f(p, w) (6), z* (7), stability (Definitions 1–2), the regularity assumptions
-- statement:
--   A ride-hailing platform chooses, in each period $t$, a price $p_t\ge 0$ per rider-hour and a wage $w_t\ge 0$ per hour of driving riders. Demand $D(p)$ and supply $S(z)$ are time-invariant functions of the price and of drivers' expected hourly earnings $z$. The **regularity assumptions** are: on $[0,\infty)$, $D$ is positive, continuous and strictly decreasing; $S$ is continuous and strictly increasing on $[0,\infty)$, positive on $(0,\infty)$, and differentiable there. The ride hours produced and the **driver utilization** are
--
--   $$Q(p,z)=\min\{D(p),S(z)\},\qquad u(p,z)=\frac{Q(p,z)}{S(z)},$$
--
--   the platform's single-period profit is $\pi(p,w,z)=(p-w)\,Q(p,z)$, the supply-unconstrained revenue is $R(p)=p\,D(p)$ and the labor cost is $C(z)=z\,S(z)$. The standing assumptions add that $R$ is unimodal with its unique maximum at $p^*\ge 0$ (strictly increasing on $[0,p^*]$, strictly decreasing on $[p^*,\infty)$), and that demand and supply cross at some $w^*\ge 0$, $D(w^*)=S(w^*)$. A function $H$ is the **inverse of the cost** if, for every $x>0$, $H(x)>0$ and $C(H(x))=x$.
--
--   A policy $(p,w,z)$ is **feasible** if $p_t,w_t\ge 0$, and **equilibrium-augmented** if drivers' earnings satisfy $z_t=w_t\,u(p_t,z_t)$ in every period. For a target $M>0$, the **minimum earnings rule** requires
--
--   $$w_{t+1}\ \ge\ \frac{M}{u(p_t,z_t)}\qquad\text{for every period }t.$$
--
--   The $M$-minimum-earnings marketplace is **stable** if some feasible equilibrium-augmented policy obeying this rule has a bounded wage sequence and nonnegative profit $\pi(p_t,w_t,z_t)\ge 0$ in all but finitely many periods.
--
--   Two explicit objects of the analysis are also defined. The **equilibrium earnings** of (6) are $f(p,w)=w$ if $S(w)<D(p)$ and $f(p,w)=H(w\,D(p))$ otherwise, and the **stability threshold** of (7) is
--
--   $$z^*=\begin{cases}w^*,&p^*\le w^*,\\ H(R(p^*)),&p^*>w^*.\end{cases}$$
--
--   This module is the common model of the three missions on this paper: the stability threshold (Theorem 1 and Lemmas 1–4), shock absorption (Theorem 2) and the equivalence with static stability (Theorem 3).
--
--   **Formalization Note** Time is indexed from $0$: Lean's period $t$ is the paper's period $t+1$, so the rule constrains every wage except the first, as (5) does ("for all $t\ge 1$"). Equilibrium also requires $z_t>0$; without it, a policy with $z_t=0$ and $S(0)=0$ would have utilization $0/0=0$ in Lean and would make every rule hold trivially. Differentiability of $S$ is required only on $(0,\infty)$, with continuity at $0$, which is weaker than the page. "Unimodal with a unique maximum at $p^*$" is read as strict monotonicity on both sides of $p^*$. The functions $D,S,H$ are defined on all of $\mathbb R$ but every assumption concerns $[0,\infty)$ (and $H$ only $(0,\infty)$); $p^*$, $w^*$ and $H$ are parameters carrying their defining properties, which determine them. The page's condition $w<S^{-1}(D(p))$ is written $S(w)<D(p)$, equivalent because $S$ is strictly increasing and defined even when $D(p)$ lies outside the range of $S$. Stability bundles Definition 1 with the rule (5) of Definition 2, since every result concerns an $M$-minimum-earnings marketplace; "bounded" is an upper bound, wages being nonnegative, and "all but finitely many $t$" is eventually along $t\to\infty$.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), pp. 6–11, (1)–(7), Definitions 1–2, Regularity assumptions (p. 8), Lemma 1 (p. 9, inverse H), Lemma 2 (p. 9, f), Theorem 1 (p. 11, z*)

import Mathlib

namespace MinEarnings.Threshold

/-- Supply-unconstrained revenue `R(p) = p · D(p)` (p. 7). -/
def revenue (D : ℝ → ℝ) (p : ℝ) : ℝ := p * D p

/-- Labor cost `C(z) = z · S(z)` (p. 7). -/
def cost (S : ℝ → ℝ) (z : ℝ) : ℝ := z * S z

/-- Regularity assumptions on the primitives (p. 8), on the domain `[0, ∞)`: demand is positive,
strictly decreasing and continuous; supply is positive on `(0, ∞)`, strictly increasing and
continuous on `[0, ∞)` and differentiable on `(0, ∞)`. -/
structure Primitives (D S : ℝ → ℝ) : Prop where
  D_pos : ∀ p, 0 ≤ p → 0 < D p
  D_strictAntiOn : StrictAntiOn D (Set.Ici 0)
  D_continuousOn : ContinuousOn D (Set.Ici 0)
  S_pos : ∀ z, 0 < z → 0 < S z
  S_strictMonoOn : StrictMonoOn S (Set.Ici 0)
  S_continuousOn : ContinuousOn S (Set.Ici 0)
  S_differentiableAt : ∀ z, 0 < z → DifferentiableAt ℝ S z

/-- The standing assumptions (p. 8): the primitives are regular, the revenue `R` is unimodal with
its unique maximum at `pStar ≥ 0` (strictly increasing on `[0, pStar]`, strictly decreasing on
`[pStar, ∞)`), and demand and supply cross at `wStar ≥ 0`. -/
structure Assumptions (D S : ℝ → ℝ) (pStar wStar : ℝ) : Prop
    extends Primitives D S where
  pStar_nonneg : 0 ≤ pStar
  revenue_strictMonoOn : StrictMonoOn (revenue D) (Set.Icc 0 pStar)
  revenue_strictAntiOn : StrictAntiOn (revenue D) (Set.Ici pStar)
  wStar_nonneg : 0 ≤ wStar
  cross : D wStar = S wStar

/-- `H` is the inverse of the cost `C` on `(0, ∞)`: for every `x > 0`, `H x > 0` and
`C(H x) = x` (Lemma 1, p. 9). -/
def IsCostInverse (S H : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → 0 < H x ∧ cost S (H x) = x

/-- Ride hours produced, `Q(p, z) = min {D(p), S(z)}` (1). -/
def quantity (D S : ℝ → ℝ) (p z : ℝ) : ℝ := min (D p) (S z)

/-- Driver utilization `u(p, z) = Q(p, z) / S(z)` (2). -/
noncomputable def util (D S : ℝ → ℝ) (p z : ℝ) : ℝ := quantity D S p z / S z

/-- Single-period profit `π(p, w, z) = (p − w) Q(p, z)` (4). -/
def profit (D S : ℝ → ℝ) (p w z : ℝ) : ℝ := (p - w) * quantity D S p z

/-- Feasible policy: `p_t ≥ 0` and `w_t ≥ 0` in every period (p. 6). Period `t` of Lean is the
paper's period `t + 1`. -/
def IsFeasible (p w : ℕ → ℝ) : Prop := ∀ t, 0 ≤ p t ∧ 0 ≤ w t

/-- Equilibrium-augmented policy: `z_t = w_t · u(p_t, z_t)` (3) in every period, with earnings
`z_t > 0` (excludes the undefined utilization `0/0` at zero supply). -/
def IsEquilibrium (D S : ℝ → ℝ) (p w z : ℕ → ℝ) : Prop :=
  ∀ t, 0 < z t ∧ z t = w t * util D S (p t) (z t)

/-- The minimum earnings rule (5): `w_{t+1} ≥ M / u(p_t, z_t)` for every period `t`; the first
wage `w 0` is unconstrained. -/
def MinEarningsRule (D S : ℝ → ℝ) (M : ℝ) (p w z : ℕ → ℝ) : Prop :=
  ∀ t, M / util D S (p t) (z t) ≤ w (t + 1)

/-- A stable policy of the `M`-minimum-earnings marketplace (Definitions 1–2): feasible,
equilibrium-augmented, satisfying rule (5), with bounded wages and non-negative profit in all but
finitely many periods. -/
def IsStablePolicy (D S : ℝ → ℝ) (M : ℝ) (p w z : ℕ → ℝ) : Prop :=
  IsFeasible p w ∧ IsEquilibrium D S p w z ∧ MinEarningsRule D S M p w z ∧
    (∃ B, ∀ t, w t ≤ B) ∧ ∀ᶠ t in Filter.atTop, 0 ≤ profit D S (p t) (w t) (z t)

/-- The `M`-minimum-earnings marketplace is stable (Definitions 1–2): some stable policy exists. -/
def IsStable (D S : ℝ → ℝ) (M : ℝ) : Prop :=
  ∃ p w z : ℕ → ℝ, IsStablePolicy D S M p w z

/-- Equilibrium earnings `f(p, w)` of (6): `w` if `S(w) < D(p)` (the page's `w < S⁻¹(D(p))`),
and `H(w · D(p))` otherwise. -/
noncomputable def eqEarnings (D S H : ℝ → ℝ) (p w : ℝ) : ℝ :=
  if S w < D p then w else H (w * D p)

/-- The stability threshold `z*` of (7): `w*` if `p* ≤ w*`, and `H(R(p*))` if `p* > w*`. -/
noncomputable def zStar (D H : ℝ → ℝ) (pStar wStar : ℝ) : ℝ :=
  if pStar ≤ wStar then wStar else H (revenue D pStar)

end MinEarnings.Threshold


