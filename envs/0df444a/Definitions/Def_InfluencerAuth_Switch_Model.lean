-- Prove2me | Definitions.Def_InfluencerAuth_Switch_Model
-- name    : InfluencerAuth_Switch_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:52.720073+00:00
-- url     : https://prove2.me/theorems/e625018e-d3f6-4a2a-9a03-57a3695d9085
-- title:
--   §3.1–3.3, Table 1, (1), (2), pp. 4–5 — policies, admissible awareness paths, discounted profit and optimality
-- statement:
--   This module sets up the influencer model of §3 of Nistor, Selove and Villas-Boas.
--
--   Time is $t\in[0,\infty)$ and the mass of potential followers is normalized to one. The influencer's **awareness** $A_t\in[0,1]$ is the fraction of potential followers who know her. At each time she is either **authentic** (endorses only products with good fit) or **inauthentic** (endorses everything). A **policy** is a measurable set $S\subseteq\mathbb R$ of times at which she is inauthentic. Following Table 1, with parameters $0<\gamma<1$ and $\varphi>1$:
--
--   1. **Followers** are $F_t=A_t$ if she is authentic and $F_t=\gamma A_t$ if she is inauthentic; the factor $f_S(t)\in\{1,\gamma\}$ is `followerFactor`.
--   2. **Instantaneous profit** is $\pi_t=A_t$ if she is authentic and $\pi_t=\gamma\varphi A_t$ if she is inauthentic (authentic profit per follower is normalized to $1$); the factor $p_S(t)\in\{1,\gamma\varphi\}$ is `profitFactor`.
--   3. An **admissible awareness path** from $A_0$ under $S$ is a function $A$, continuous on $[0,\infty)$, with $A(0)=A_0$ and values in $[0,1]$, solving the equation of motion (1), $\frac{dA_t}{dt}=\beta F_t(1-A_t)$, in integral form:
--   $$
--   A_t=A_0+\int_0^t \beta\, f_S(s)\,A_s\,(1-A_s)\,ds\qquad(t\ge 0).
--   $$
--   4. The **discounted profit** (2) at time $0$, with discount rate $r$, is
--   $$
--   J(S,A)=\int_0^\infty e^{-ru}\,p_S(u)\,A_u\,du .
--   $$
--   5. A pair $(S,A)$ is **optimal from $A_0$** if it is admissible from $A_0$ and $J(S',A')\le J(S,A)$ for every admissible pair $(S',A')$ from $A_0$.
--
--   These objects are the vocabulary of Proposition 1 and of every lemma of §3.3: "the influencer is always authentic" means that the policy $S=\emptyset$ is optimal, and "always inauthentic" means that $S=\mathbb R$ is optimal.
--
--   **Formalization Note** The paper leaves the policy class implicit ("continuously decides"); measurable sets of times are the broadest open-loop class, and a feedback rule is expressed through the path it drives. Because a measurable control makes $dA/dt$ exist only almost everywhere, (1) is imposed in integral (Carathéodory) form rather than as a pointwise derivative, which would exclude every switching policy at its switching time. The clause $A_t\in[0,1]$ is implied by the equation for $0<A_0<1$; it is stated so that every profit stream is visibly bounded and integrable. Measurability of $S$ is part of admissibility, so no competitor's profit is a junk value. The paper's $V_t$ at a general $t$ is the same object after the shift $s=u-t$.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), §3.1–3.3, Table 1, (1), (2), pp. 4–5

import Mathlib

open MeasureTheory Set

namespace InfluencerAuth.Switch

/-- Follower factor of Table 1 (p. 5): an influencer who is inauthentic at time `t`
(`t ∈ S`) has `γ A_t` followers, an authentic one has `A_t`. -/
noncomputable def followerFactor (γ : ℝ) (S : Set ℝ) (t : ℝ) : ℝ :=
  open Classical in if t ∈ S then γ else 1

/-- Profit factor of Table 1 (p. 5): instantaneous profit is `γ φ A_t` when inauthentic
(`t ∈ S`) and `A_t` when authentic (authentic profit per follower normalized to 1, p. 4). -/
noncomputable def profitFactor (γ φ : ℝ) (S : Set ℝ) (t : ℝ) : ℝ :=
  open Classical in if t ∈ S then γ * φ else 1

/-- Admissible awareness path under the policy `S` (the measurable set of times at which
the influencer is inauthentic), started at `A₀`: a Carathéodory solution on `[0, ∞)` of
the equation of motion (1), `dA_t/dt = β F_t (1 - A_t)` with `F_t = followerFactor γ S t * A_t`,
written in integral form, continuous, with values in `[0, 1]`. -/
def IsPath (β γ A₀ : ℝ) (S : Set ℝ) (A : ℝ → ℝ) : Prop :=
  MeasurableSet S ∧
  ContinuousOn A (Set.Ici 0) ∧
  A 0 = A₀ ∧
  (∀ t : ℝ, 0 ≤ t → A t ∈ Set.Icc (0 : ℝ) 1) ∧
  ∀ t : ℝ, 0 ≤ t →
    A t = A₀ + ∫ s in (0 : ℝ)..t, β * followerFactor γ S s * A s * (1 - A s)

/-- Discounted profit (2) at time `0`: `∫_0^∞ e^{-r u} π_u du` with `π_u = profitFactor γ φ S u * A_u`. -/
noncomputable def discountedProfit (γ φ r : ℝ) (S : Set ℝ) (A : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-r * t) * profitFactor γ φ S t * A t

/-- The policy `S` with its path `A` is optimal from initial awareness `A₀`: it is admissible,
and no admissible policy–path pair from `A₀` earns a larger discounted profit. -/
def IsOptimalFrom (β γ φ r A₀ : ℝ) (S : Set ℝ) (A : ℝ → ℝ) : Prop :=
  IsPath β γ A₀ S A ∧
  ∀ (S' : Set ℝ) (A' : ℝ → ℝ), IsPath β γ A₀ S' A' →
    discountedProfit γ φ r S' A' ≤ discountedProfit γ φ r S A

end InfluencerAuth.Switch


