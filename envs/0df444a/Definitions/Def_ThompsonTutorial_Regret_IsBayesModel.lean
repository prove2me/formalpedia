-- Prove2me | Definitions.Def_ThompsonTutorial_Regret_IsBayesModel
-- name    : ThompsonTutorial_Regret_IsBayesModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:11:37.382862+00:00
-- url     : https://prove2.me/theorems/655555f6-bf90-481b-8984-c544600206e7
-- title:
--   The Bayesian model $y_t=g(x_t,\theta,w_t)$ of an online decision problem
-- statement:
--   On a probability space $(\Omega,\mathcal F,\mathbb P)$, let $\theta:\Omega\to\Theta$ be the unknown parameter, $w_t:\Omega\to W$ the disturbance of period $t$, $g:\mathcal X\times\Theta\times W\to Y$ the known outcome function and $r:Y\to\mathbb R$ the known reward. The model of §8.1.2 holds when
--
--   1. $\theta$ and every $w_t$ are random variables, $g$ is jointly measurable and $r$ is measurable;
--   2. the disturbances $w_1,w_2,\dots$ are mutually independent and identically distributed;
--   3. $\theta$ is independent of the whole sequence $(w_1,w_2,\dots)$.
--
--   The outcome of action $x_t$ in period $t$ is then $y_t=g(x_t,\theta,w_t)$ and its reward is $r(y_t)$. This is the paper's general Bayesian model of an online decision problem: $\theta$ represents the uncertain characteristics of the system and $w_t$ the idiosyncratic randomness of period $t$.
--
--   **Formalization Note** Periods are 1-based; $w_0$ is unconstrained and never used. The spaces $\Theta,\mathcal X,Y,W$ are arbitrary measurable spaces (no finiteness or standard-Borel assumption). Measurability is the standing convention implicit in the paper's random variables.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), doi:10.1561/2200000070, §8.1.2 Problem Formulation, p. 70 (PDF p. 73); general setting of Ch. 4, p. 18 (PDF p. 21)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace ThompsonTutorial.Regret

/-- **The Bayesian model of an online decision problem.**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2 "Problem Formulation", p. 70 (PDF p. 73): "In each period t ∈ N, the
agent selects an action xt ∈ X, observes an outcome yt, and associates this with a real-valued
reward r(yt) that is a known function of the outcome. [...] More generally, for each t,
yt = g(xt, θ, wt) where g is some known function and (wt : t ∈ N) are i.i.d and independent of θ.
This can be thought of as a Bayesian model, where the random variable θ represents the uncertain
true characteristics of the system and wt represents idiosyncratic randomness influencing the
outcome in period t."

`IsBayesModel P θ w g r` says, on the probability space `(Ω, P)`:
1. the parameter `θ : Ω → Θ` and every disturbance `w t : Ω → W` are random variables;
2. the outcome function `g : X → Θ → W → Y` is jointly measurable and the reward `r : Y → ℝ` is
   measurable;
3. the disturbances `w 1, w 2, …` are mutually independent and identically distributed;
4. `θ` is independent of the whole disturbance sequence `(w 1, w 2, …)`.

**Formalization Note.** Periods are 1-based (the paper's `t ∈ N` starts at 1): the disturbance of
period `t` is `w t` for `t ≥ 1`, and `w 0` is unconstrained and never used. The action set `X`,
the parameter space `Θ`, the outcome space `Y` and the noise space `W` are arbitrary measurable
spaces (no finiteness, countability or standard-Borel assumption); measurability of `θ`, `w t`,
`g` and `r` is the convention implicit in the paper's "random variable" and in the expectations
it writes. -/
def IsBayesModel {Ω Θ X Y W : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (P : Measure Ω) (θ : Ω → Θ) (w : ℕ → Ω → W) (g : X → Θ → W → Y) (r : Y → ℝ) : Prop :=
  Measurable θ ∧ (∀ t, Measurable (w t)) ∧
  Measurable (fun p : X × Θ × W => g p.1 p.2.1 p.2.2) ∧ Measurable r ∧
  iIndepFun (fun (i : ℕ) => w (i + 1)) P ∧
  (∀ i : ℕ, IdentDistrib (w (i + 1)) (w 1) P P) ∧
  IndepFun θ (fun ω (i : ℕ) => w (i + 1) ω) P

end ThompsonTutorial.Regret


