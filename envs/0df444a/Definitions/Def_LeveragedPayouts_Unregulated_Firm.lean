-- Prove2me | Definitions.Def_LeveragedPayouts_Unregulated_Firm
-- name    : LeveragedPayouts_Unregulated_Firm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:20.530691+00:00
-- url     : https://prove2.me/theorems/8bb17c15-0968-476d-a2d3-987820f26f6c
-- title:
--   §2.1 and §3.4.3 — the firm's programs (3), (5)–(6) and the date-0 entrepreneur's program (31)–(32)
-- statement:
--   The firm's (partial-equilibrium) programs of §2.1 and the date-0 entrepreneur's program of §3.4.3.
--
--   A shareholder discounts date-1 consumption at $R>1$ and controls the success probability $e$ of a technology $f$ at private cost $e^2 f(I)/(2\pi R)$, with $\pi\in(0,1)$. The firm faces the market rate $r>0$ and holds a risk-free endowment $W$.
--
--   1. **Incentive constraint** (6)/(32). Given a retained stake $x$, the effort $e$ is incentive-compatible when
--   $$e=\arg\max_y\Big\{xy-\frac{y^2}{2\pi}\Big\},$$
--   i.e. $xy-y^2/(2\pi)\le xe-e^2/(2\pi)$ for every real $y$.
--   2. **Program (3)** (case $r\ge R$): maximize over $e\in[0,1]$ and $I>0$
--   $$\frac{(e-e^2/(2\pi))f(I)+W-rI}{R}.$$
--   3. **Program (5)–(6)** (case $r<R$): maximize over $x\in[0,1]$, $I>0$ and incentive-compatible $e$
--   $$\frac{W+(1-x)ef(I)}{r}-I+\Big(xe-\frac{e^2}{2\pi}\Big)\frac{f(I)}{R}.$$
--   4. **Program (31)–(32)** (a date-0 entrepreneur facing the rate $r_0$ and the rigid wage $w^*$, investing $I=w^*l$): maximize over $x\in[0,1]$, $l>0$ and incentive-compatible $e$
--   $$\frac{W+(1-x)ef(l)}{r_0}-w^*l+\Big(xe-\frac{e^2}{2\pi}\Big)\frac{f(l)}{R}.$$
--
--   The predicates `IsMax3`, `IsMax5`, `IsMax31` say that a feasible point attains the maximum of the corresponding program.
--
--   **Formalization Note** $x\in[0,1]$ is the retained fraction of output (p. 14) and $e\in[0,1]$ in (3) is a probability; the unconstrained maximizer $\pi$ lies inside. The paper's restriction "$W>rI$" (risk-free debt) is not imposed: $W$ enters every objective additively and does not affect the maximizers.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), pp. 13–14, (3), (5), (6); p. 29, (31), (32)

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.Unregulated

/-- The incentive constraint (6)/(32): `e = argmax_y {x y − y²/(2π)}`, i.e. `e` maximizes the
shareholder's utility net of effort cost given her retained stake `x`. -/
def IsIC (π x e : ℝ) : Prop :=
  ∀ y : ℝ, x * y - y ^ 2 / (2 * π) ≤ x * e - e ^ 2 / (2 * π)

/-- The objective (3) of the firm when `r ≥ R`: `[(e − e²/(2π)) f(I) + W − r I]/R`. -/
noncomputable def obj3 (π R W r : ℝ) (f : ℝ → ℝ) (e I : ℝ) : ℝ :=
  ((e - e ^ 2 / (2 * π)) * f I + W - r * I) / R

/-- The objective (5) of the firm when `r < R`:
`[W + (1 − x) e f(I)]/r − I + (x e − e²/(2π)) f(I)/R`. -/
noncomputable def obj5 (π R W r : ℝ) (f : ℝ → ℝ) (e I x : ℝ) : ℝ :=
  (W + (1 - x) * e * f I) / r - I + (x * e - e ^ 2 / (2 * π)) * f I / R

/-- The objective (31) of a date-0 entrepreneur facing the rate `r₀` and the rigid wage `w*`:
`[W + (1 − x) e f(l)]/r₀ − w* l + (x e − e²/(2π)) f(l)/R`. -/
noncomputable def obj31 (E : Economy) (W r₀ : ℝ) (e l x : ℝ) : ℝ :=
  (W + (1 - x) * e * E.f l) / r₀ - E.wstar * l + (x * e - e ^ 2 / (2 * E.π)) * E.f l / E.R

/-- `(e, I)` solves program (3): `e ∈ [0, 1]` (a probability), `I > 0`, and no feasible `(e', I')`
does better. -/
def IsMax3 (π R W r : ℝ) (f : ℝ → ℝ) (e I : ℝ) : Prop :=
  0 ≤ e ∧ e ≤ 1 ∧ 0 < I ∧
    ∀ e' I', 0 ≤ e' → e' ≤ 1 → 0 < I' → obj3 π R W r f e' I' ≤ obj3 π R W r f e I

/-- `(e, I, x)` solves program (5)–(6): `x ∈ [0, 1]`, `I > 0`, `e` incentive-compatible (6), and no
feasible `(e', I', x')` does better. -/
def IsMax5 (π R W r : ℝ) (f : ℝ → ℝ) (e I x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ 0 < I ∧ IsIC π x e ∧
    ∀ e' I' x', 0 ≤ x' → x' ≤ 1 → 0 < I' → IsIC π x' e' →
      obj5 π R W r f e' I' x' ≤ obj5 π R W r f e I x

/-- `(e, l, x)` solves program (31)–(32): `x ∈ [0, 1]`, `l > 0`, `e` incentive-compatible (32), and
no feasible `(e', l', x')` does better. -/
def IsMax31 (E : Economy) (W r₀ : ℝ) (e l x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ 0 < l ∧ IsIC E.π x e ∧
    ∀ e' l' x', 0 ≤ x' → x' ≤ 1 → 0 < l' → IsIC E.π x' e' →
      obj31 E W r₀ e' l' x' ≤ obj31 E W r₀ e l x

end LeveragedPayouts.Unregulated


