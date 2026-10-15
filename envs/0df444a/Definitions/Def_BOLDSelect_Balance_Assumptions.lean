-- Prove2me | Definitions.Def_BOLDSelect_Balance_Assumptions
-- name    : BOLDSelect_Balance_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:46.349164+00:00
-- url     : https://prove2.me/theorems/11540b86-7879-4135-ac03-fb73d8c61a1a
-- title:
--   §4, pp. 3373–3374 — Assumptions 1–4 on the rate functions, with $H_x = [a_x, b_x]$
-- statement:
--   This file states the four assumptions of Chen and Ryzhov's analysis of the BOLD allocation, together with the standing convention of the paper's model on the parameter space of each distributional family.
--
--   Each alternative $x$ has a family of laws $F_x(\theta)$ with rate function $I_x(u;\theta)$, derivative $D_x(u;\theta) = \partial I_x/\partial u$ and effective domain $\mathcal D_x$ (the interior of the set where $I_x$ is finite). For each $x$ fix a compact interval $H_x = [a_x,b_x]$; the theorems take $a_x < b_x$ and the true mean $\mu_x$ in the interior $(a_x,b_x)$.
--
--   **Standing convention (parameter space).** For each $x$ there is an open interval $\Theta_x$ of mean parameters such that:
--   1. $H_x \subseteq \Theta_x$, and every sample of $x$ lies in $\Theta_x$ almost surely ($F_x(\mu_x)(\mathbb R\setminus\Theta_x) = 0$), so every sample mean of $x$ lies in $\Theta_x$ too;
--   2. for $\theta \in \Theta_x$, $F_x(\theta)$ is integrable with mean $\theta$;
--   3. for $\theta \in \Theta_x$, $\theta' \in \Theta_y$ and every $u$ between $\theta$ and $\theta'$, the pair $(u,\theta)$ lies in $\mathcal D_x$. This makes equation (10) an equation in genuine derivatives between any two plug-in means.
--
--   **Assumption 1.** For every $x$ and every $\varepsilon > 0$,
--   $$\inf_{\theta\in H_x,\ |u-\theta|>\varepsilon} I_x(u;\theta) > 0, \qquad \inf_{\theta\in H_x,\ |u-\theta|>\varepsilon} |D_x(u;\theta)| > 0,$$
--   the second infimum taken over pairs in $\mathcal D_x$.
--
--   **Assumption 2.** $I_x$ and $D_x$ are continuous (jointly in $(u,\theta)$) at every pair $(u,\theta) \in \mathcal D_x$ with $\theta \in H_x$; and for every $\varepsilon > 0$ there is $\delta > 0$ such that $\theta \in H_x$ and $|u-\theta| < \delta$ imply $I_x(u;\theta) < \varepsilon$ and $|D_x(u;\theta)| < \varepsilon$.
--
--   **Assumption 3.** For any $x, y$ there is a constant $C > 0$ such that
--   $$\sup_{u\neq\theta}\left|\frac{D_x(u;\theta)}{D_y(\theta;u)}\right| \le C,$$
--   the supremum over $u \ne \theta$ with $(u,\theta) \in \mathcal D_x$ and $(\theta,u) \in \mathcal D_y$.
--
--   **Assumption 4.** For every $x$, the partial derivatives $\partial I_x/\partial\theta\,(u;\theta)$ and $\partial D_x/\partial\theta\,(u;\theta)$ are continuously differentiable jointly in $(u,\theta)$ on $\mathcal D_x$.
--
--   Assumptions 1–2 make $I_x(\cdot;\theta)$ vanish exactly at $u=\theta$ and behave well near it; Assumption 3 keeps two alternatives from being "mistaken" for each other when one's sample mean meets the other's true value, which matters for discrete laws such as Bernoulli. Theorems 1–2 use Assumptions 1–3, Theorems 3–4 use Assumptions 1–4.
--
--   **Formalization Note** The paper's "$H$ is any closed interval with non-empty interior containing $\mu_x$" is read as one fixed interval $H_x$ per alternative, with $\mu_x$ in its interior, shared by Assumptions 1 and 2; reading it as "every such interval" would require the assumptions up to the edge of the parameter range, which bounded families (for instance exponential laws indexed by a mean $\theta>0$) do not satisfy. A positive infimum is written as a uniform positive lower bound. Conditions on $D_x$ (Assumptions 1–3) and Assumption 4 are imposed on the effective domain, where $D_x$ is a genuine derivative; for a normal family this is everything, for a Bernoulli family $(0,1)^2$. Assumption 3 is written without division, $|D_x(u;\theta)| \le C\,|D_y(\theta;u)|$, which agrees with the quotient where $D_y(\theta;u) \ne 0$ and forbids $D_x \ne 0 = D_y$, as an infinite quotient would. Assumption 3 is required for all $x, y$, including $x = y$, as printed. The parameter-space convention is not printed as an assumption. It makes explicit the paper's definition of $I^n_x$ as the rate function of the family member whose mean is the current sample mean, and the implicit premise of (4), (9) and (10) that the rate functions are finite between the means. It is needed for the theorems to hold. Without it, a law in the family evaluated at a sample mean outside $H_x$ could have $I_x = +\infty$ off a single point, which makes $\Gamma^n_{x^{*,n},x} = +\infty$ forever, and that alternative is never sampled again. Bernoulli laws are an example: a sample mean of $0$ gives $I_x(u;0) = +\infty$ for $u > 0$. Such laws are therefore outside the convention; see the mission's moderation notes.
-- source:
--   Chen & Ryzhov, Balancing Optimal Large Deviations in Ranking and Selection, Proc. 2019 Winter Simulation Conference, pp. 3373–3374, §4, Assumptions 1–4; standing conventions from pp. 3370–3371, §2, (4), (9)–(10)

import Mathlib
import Definitions.Def_BOLDSelect_Balance_RateFunction

open MeasureTheory
open scoped ENNReal

namespace BOLDSelect.Balance

/-!
Chen & Ryzhov, *Balancing Optimal Large Deviations in Ranking and Selection*, Proc. 2019 Winter
Simulation Conference, §4, Assumptions 1–4 (pp. 3373–3374), and the standing convention of §2–§3
on the parameter space of each family.

For each alternative `x` the interval `H` of Assumptions 1–2 is one fixed compact interval
`H_x = [a x, b x]`; the theorems require `a x < b x` and `µ x ∈ (a x, b x)`.
Pointwise conditions on `D_x` are imposed on the effective domain `effDom Fam x`, where `I_x` is
finite near `(u, θ)` (for a normal family this is everything).
-/

/-- Standing convention on the parameter space (§2–§3, pp. 3369–3372; not printed as an assumption).
For each `x`, `Θ x` is an open interval of mean parameters such that
* it contains `H_x = [a x, b x]`, and every sample of `x` lies in it almost surely
  (`F_x(µ_x)(ℝ ∖ Θ_x) = 0`), so every sample mean of `x` lies in it as well;
* for `θ ∈ Θ_x` the member `Fam x θ` is integrable with mean `θ`, so that the plug-in
  `I_x(·;θ^n_x)` is the rate function of the member with mean `θ^n_x` (p. 3371);
* for `θ ∈ Θ_x`, `θ' ∈ Θ_y` and every `u` between them, `I_x(·;θ)` is finite near `(u, θ)`,
  so that (10) is an equation in genuine derivatives between any two plug-in means (the premise of
  (4) and (9)–(10)). -/
def ParameterSpace {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (μ : Fin M → ℝ) (Θ : Fin M → Set ℝ)
    (a b : Fin M → ℝ) : Prop :=
  (∀ x, IsOpen (Θ x) ∧ (Θ x).OrdConnected ∧ Set.Icc (a x) (b x) ⊆ Θ x ∧
    (Fam x (μ x)) (Θ x)ᶜ = 0) ∧
  (∀ x, ∀ θ ∈ Θ x, Integrable id (Fam x θ) ∧ ∫ t, t ∂(Fam x θ) = θ) ∧
  (∀ x y, ∀ θ ∈ Θ x, ∀ θ' ∈ Θ y, ∀ u ∈ Set.uIcc θ θ', (u, θ) ∈ effDom Fam x)

/-- Assumption 1 (p. 3373): for every `x` and every `ε > 0`,
`inf_{θ ∈ H, |u−θ| > ε} I_x(u;θ) > 0` and `inf_{θ ∈ H, |u−θ| > ε} |D_x(u;θ)| > 0`,
each infimum being positive written as a uniform positive lower bound `c`. -/
def Assumption1 {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (a b : Fin M → ℝ) : Prop :=
  ∀ x, ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ θ ∈ Set.Icc (a x) (b x), ∀ u : ℝ, ε < |u - θ| →
      (c : EReal) ≤ rateI Fam x u θ ∧ ((u, θ) ∈ effDom Fam x → c ≤ |rateD Fam x u θ|)

/-- Assumption 2 (p. 3373): `I_x` and `D_x` are continuous at every `(u, θ)` with `θ ∈ H_x`
(in the effective domain), and for every `ε > 0` there is `δ > 0` such that `θ ∈ H_x` and
`|u − θ| < δ` imply `I_x(u;θ) < ε` and `|D_x(u;θ)| < ε`. -/
def Assumption2 {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (a b : Fin M → ℝ) : Prop :=
  ∀ x,
    (∀ θ ∈ Set.Icc (a x) (b x), ∀ u : ℝ, (u, θ) ∈ effDom Fam x →
      ContinuousAt (fun p : ℝ × ℝ => rateI Fam x p.1 p.2) (u, θ) ∧
      ContinuousAt (fun p : ℝ × ℝ => rateD Fam x p.1 p.2) (u, θ)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ θ ∈ Set.Icc (a x) (b x), ∀ u : ℝ, |u - θ| < δ →
        rateI Fam x u θ < (ε : EReal) ∧ |rateD Fam x u θ| < ε

/-- Assumption 3 (p. 3374): for any `x, y` there is a constant `C > 0` with
`sup_{u ≠ θ} |D_x(u;θ) / D_y(θ;u)| ≤ C`, written without division as
`|D_x(u;θ)| ≤ C |D_y(θ;u)|` (note the swapped arguments of `D_y`), for `u ≠ θ` in the effective
domains of both functions. -/
def Assumption3 {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) : Prop :=
  ∀ x y, ∃ C : ℝ, 0 < C ∧ ∀ u θ : ℝ, u ≠ θ → (u, θ) ∈ effDom Fam x → (θ, u) ∈ effDom Fam y →
    |rateD Fam x u θ| ≤ C * |rateD Fam y θ u|

/-- Assumption 4 (p. 3374): for every `x`, `∂I_x/∂θ (u;θ)` and `∂D_x/∂θ (u;θ)` are continuously
differentiable jointly in `(u, θ)` on the effective domain. -/
def Assumption4 {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) : Prop :=
  ∀ x,
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => deriv (fun t => (rateI Fam x p.1 t).toReal) p.2)
      (effDom Fam x) ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => deriv (fun t => rateD Fam x p.1 t) p.2) (effDom Fam x)

end BOLDSelect.Balance


