-- Prove2me | Definitions.Def_InfluencerAuth_Turnover_Model
-- name    : InfluencerAuth_Turnover_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:30:21.233824+00:00
-- url     : https://prove2.me/theorems/1c6c1d30-baca-40cf-bd4a-708166e953fe
-- title:
--   §3, §4.2, Table 1, (2), (6), Lemma 5, Condition 2, pp. 4–5, 9 — policies, awareness paths under turnover, discounted profit, optimality, V̄ and Condition 2
-- statement:
--   This file sets up the influencer model of Nistor, Selove and Villas-Boas with follower turnover (§4.2).
--
--   Time is $t \in [0,\infty)$. There is a unit mass of potential followers, and $A_t \in [0,1]$ is the share of them who are aware of the influencer. At each time she is either **authentic** or **inauthentic**. A **policy** is a measurable set $S \subseteq \mathbb R$ of the times at which she is inauthentic; $S = \emptyset$ is "always authentic". Following Table 1 (p. 5), the number of followers is $F_t = f_S(t)\,A_t$ and the instantaneous profit is $\pi_t = p_S(t)\,A_t$, where
--   $$
--   f_S(t) = \begin{cases}\gamma, & t \in S,\\ 1, & t \notin S,\end{cases}\qquad
--   p_S(t) = \begin{cases}\gamma\varphi, & t \in S,\\ 1, & t \notin S.\end{cases}
--   $$
--   The parameters $\gamma$ and $\varphi$ are the reduced-form parameters of §3.1 (a fraction $\gamma$ of aware people follow an inauthentic influencer, who earns $\varphi$ per follower; authentic profit per follower is normalized to $1$).
--
--   1. **Admissible awareness path.** Given an initial awareness $A_0$, a function $A$ is an admissible path under $S$ with turnover rate $x$ if it is continuous on $[0,\infty)$, $A(0) = A_0$, $A_t \in [0,1]$ for $t \ge 0$, and for every $t \ge 0$
--   $$
--   A_t = A_0 + \int_0^t \bigl(\beta f_S(s) A_s (1 - A_s) - x A_s\bigr)\,ds,
--   $$
--   the integral form of the equation of motion (6), $\frac{dA_t}{dt} = \beta F_t(1 - A_t) - x A_t$.
--   2. **Discounted profit** (2) at time $0$: $\displaystyle J(S, A) = \int_0^\infty e^{-r t}\, p_S(t)\, A_t\,dt$.
--   3. **Optimality from $A_0$.** $(S, A)$ is optimal from $A_0$ if $S$ is measurable, $A$ is an admissible path from $A_0$ under $S$, and $J(S', A') \le J(S, A)$ for every measurable policy $S'$ and every admissible path $A'$ from $A_0$ under $S'$.
--   4. **The always-authentic value** of Lemma 5 (p. 9), written in the variable $s = u - t$:
--   $$
--   \overline V(A_0) = \int_0^\infty \frac{e^{-r s}}{\dfrac{\beta}{\beta - x} + \dfrac{1 - A_0\frac{\beta}{\beta - x}}{A_0}\, e^{-(\beta - x) s}}\,ds .
--   $$
--   5. **Condition 2** (p. 9): $\dfrac{(1-\gamma)x}{r + \beta - x} > \gamma\varphi - 1$.
--
--   These objects are shared by every statement of the mission: Lemma 5 identifies $J(\emptyset, A)$ with $\overline V(A_0)$, display (7) differentiates $\overline V$ at the steady state, and Proposition 3 asserts that $(\emptyset, A)$ is optimal under Condition 2.
--
--   **Formalization Note** The equation of motion is imposed in integral (Carathéodory) form because a measurable policy makes $dA_t/dt$ exist only almost everywhere; requiring a derivative everywhere would exclude every switching policy. The clause $A_t \in [0,1]$ is implied by the equation when $0 < A_0 < 1$; it is stated so that every profit stream is visibly bounded and integrable. Lean's interval integral of a non-integrable function is $0$, so the definition of optimality requires measurable policies; for those, every integrand above is integrable. $\overline V$ is a plain function of $A_0$ (with $\beta, x, r$ as parameters); the paper's $\overline V(A_t)$ at a later time $t$ is the same function evaluated at the current awareness.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), §3.1–3.3, Table 1, (2), pp. 4–5; §4.2, (6), Lemma 5, Condition 2, p. 9

import Mathlib
import Definitions.Def_InfluencerAuth_Switch_Model

namespace InfluencerAuth.Turnover

open MeasureTheory

/-- `A` is an admissible awareness path from `A₀` under the policy `S` with turnover rate `x`:
continuous on `[0, ∞)`, starts at `A₀`, stays in `[0, 1]`, and solves the integral form of the
equation of motion (6), `dA/dt = β F_t (1 - A_t) - x A_t` with `F_t = InfluencerAuth.Switch.followerFactor γ S t * A_t`. -/
def IsPath (β γ x A₀ : ℝ) (S : Set ℝ) (A : ℝ → ℝ) : Prop :=
  ContinuousOn A (Set.Ici 0) ∧ A 0 = A₀ ∧
    (∀ t : ℝ, 0 ≤ t → A t ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ t : ℝ, 0 ≤ t →
      A t = A₀ + ∫ s in (0 : ℝ)..t, (β * InfluencerAuth.Switch.followerFactor γ S s * A s * (1 - A s) - x * A s)

/-- The pair `(S, A)` is optimal from initial awareness `A₀`: `S` is a measurable policy, `A` is
its admissible path from `A₀`, and no measurable policy with an admissible path from `A₀` earns
a larger discounted profit. -/
def IsOptimalFrom (β γ φ r x A₀ : ℝ) (S : Set ℝ) (A : ℝ → ℝ) : Prop :=
  MeasurableSet S ∧ IsPath β γ x A₀ S A ∧
    ∀ (S' : Set ℝ) (A' : ℝ → ℝ), MeasurableSet S' → IsPath β γ x A₀ S' A' →
      InfluencerAuth.Switch.discountedProfit γ φ r S' A' ≤ InfluencerAuth.Switch.discountedProfit γ φ r S A

/-- The right-hand side of Lemma 5 (p. 9), in the variable `s = u - t`:
`V̄(A₀) = ∫_0^∞ e^{-r s} / [β/(β-x) + ((1 - A₀ β/(β-x)) / A₀) e^{-(β-x) s}] ds`. -/
noncomputable def authValue (β x r A₀ : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ),
    Real.exp (-r * s) /
      (β / (β - x) + ((1 - A₀ * (β / (β - x))) / A₀) * Real.exp (-(β - x) * s))

/-- Condition 2 (p. 9): `(1 - γ) x / (r + β - x) > γ φ - 1`. -/
def Condition2 (γ φ β r x : ℝ) : Prop :=
  (1 - γ) * x / (r + β - x) > γ * φ - 1

end InfluencerAuth.Turnover


