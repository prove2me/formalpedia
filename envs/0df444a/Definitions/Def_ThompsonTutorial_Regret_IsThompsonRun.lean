-- Prove2me | Definitions.Def_ThompsonTutorial_Regret_IsThompsonRun
-- name    : ThompsonTutorial_Regret_IsThompsonRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:12:23.420234+00:00
-- url     : https://prove2.me/theorems/7ac6990f-35d5-49c7-95c8-7fc358f9ca48
-- title:
--   A run of Thompson sampling (Algorithm 4)
-- statement:
--   In the model above, let $f:\Theta\to\mathcal X$, let $\hat\theta_t:\Omega\to\Theta$ be the samples and $x_t:\Omega\to\mathcal X$ the actions ($t\ge1$). Write $\mu$ for the mean reward and $H_{t-1}$ for the history. The actions are a run of Thompson sampling when
--
--   1. (line 6, the argmax) $f$ is measurable and $\mu(x,\vartheta)\le\mu(f(\vartheta),\vartheta)$ for all $\vartheta,x$;
--   2. (lines 3 and 6) for each $t\ge1$, $\hat\theta_t$ is a random variable and $x_t=f(\hat\theta_t)$;
--   3. (line 3, $\hat\theta\sim p$ with $p$ the posterior) for each $t\ge1$ and measurable $A\subseteq\Theta$,
--   $$\mathbb P(\hat\theta_t\in A\mid H_{t-1})=\mathbb P(\theta\in A\mid H_{t-1})\quad\text{a.s.};$$
--   4. (line 3, fresh randomness) for each $t\ge1$, $\hat\theta_t$ is conditionally independent of $(\theta,(w_s)_{s\ge1})$ given $H_{t-1}$: for measurable $A\subseteq\Theta$ and $C\subseteq\Theta\times W^{\mathbb N}$,
--   $$\mathbb P(\hat\theta_t\in A,\ (\theta,w)\in C\mid H_{t-1})=\mathbb P(\hat\theta_t\in A\mid H_{t-1})\,\mathbb P((\theta,w)\in C\mid H_{t-1})\quad\text{a.s.}$$
--
--   Algorithm 4 samples a model from the current distribution $p$, acts greedily for it, and updates $p$ by Bayes' rule; iterating the update makes $p$ the posterior of $\theta$ given $H_{t-1}$, which is what clause 3 encodes.
--
--   **Formalization Note** Conditional laws are stated set-wise through conditional expectations of indicators, so no regular conditional distribution and no standard-Borel hypothesis is needed. Clause 4 excludes oracle samples such as $\hat\theta_t=\theta$. The selector $f$ is also used for the optimal action $x^*=f(\theta)$ in the theorems, so ties are broken the same way. Every run of Algorithm 4 with a measurable tie-breaking rule satisfies clauses 1–4; the clauses do not require $\hat\theta_t$ to be independent of earlier samples beyond what $H_{t-1}$ records.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), doi:10.1561/2200000070, Ch. 4, Algorithm 4, p. 19 (PDF p. 22); Ch. 5, p. 27 (PDF p. 30); model of §8.1.2, p. 70 (PDF p. 73)

import Mathlib
import Definitions.Def_ThompsonTutorial_Regret_meanReward
import Definitions.Def_ThompsonTutorial_Regret_history
open MeasureTheory

namespace ThompsonTutorial.Regret

/-- **A run of Thompson sampling (Algorithm 4).**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), Ch. 4, Algorithm 4 "Thompson(X, p, q, r)", p. 19 (PDF p. 22):
"for t = 1, 2, . . . do: Sample θ̂ ∼ p; xt ← argmax_{x∈X} E_{q_θ̂}[r(yt)|xt = x]; Apply xt and
observe yt; p ← P_{p,q}(θ ∈ ·|xt, yt)"; in the model of §8.1.2, p. 70 (PDF p. 73), where
`E_{q_θ̂}[r(y_t) | x_t = x] = µ(x, θ̂)`. Ch. 5, p. 27 (PDF p. 30): "TS generates an action xt by
sampling a parameter vector θ̂ from ft−1", the posterior of θ given `H_{t−1}`.

`IsThompsonRun P θ w g r f θhat xs` says that the actions `xs t` (`t ≥ 1`) are produced by
Thompson sampling with the samples `θhat t`, in the model with parameter `θ`, disturbances `w`,
outcome function `g` and reward `r`. Writing `µ = meanReward P w g r` and `H_{t−1}` for
`history g θ w xs t`:
1. (line 6, the argmax) `f : Θ → X` is a measurable selector of `argmax_x µ(x, ϑ)`:
   `µ(x, ϑ) ≤ µ(f ϑ, ϑ)` for all `ϑ` and `x`;
2. (lines 3 and 6) for every period `t ≥ 1`, the sample `θhat t` is a random variable and the
   action is `x_t = f(θhat t)`;
3. (line 3, `θ̂ ∼ p` with `p` the posterior) for every `t ≥ 1` and measurable `A ⊆ Θ`,
   `P(θhat t ∈ A | H_{t−1}) = P(θ ∈ A | H_{t−1})` almost surely;
4. (line 3, the sample uses fresh randomness) for every `t ≥ 1`, `θhat t` is conditionally
   independent of `(θ, (w_s)_{s ≥ 1})` given `H_{t−1}`: for measurable `A ⊆ Θ` and
   `C ⊆ Θ × (ℕ → W)`,
   `P(θhat t ∈ A, (θ, w) ∈ C | H_{t−1}) = P(θhat t ∈ A | H_{t−1}) · P((θ, w) ∈ C | H_{t−1})` a.s.

**Formalization Note.** The distribution `p` of Algorithm 4 at the start of period `t` is the
posterior `P(θ ∈ · | H_{t−1})` (line 10 iterated); it is encoded through conditional
expectations of indicators rather than through the recursive Bayes update (4.2), which needs
densities and agrees with it whenever it is defined. Conditional laws are stated set-wise, so no
regular conditional distribution (and no standard-Borel hypothesis on any space) is needed.
Clause 4 rules out "oracle" samples such as `θhat t = θ`. Every run of Algorithm 4 whose argmax
is computed by a measurable tie-breaking rule `f` satisfies clauses 1–4; the clauses do not
require `θhat t` to be independent of the earlier samples `θhat s` beyond what `H_{t−1}` records,
so the class is slightly larger than the paper's. The same selector `f` is used to
define the optimal action `x* = f(θ)` in the theorems: ties in the argmax are broken in the same
way for `x*` and for Thompson sampling. In the sequence `w`, index `i` stands for `w (i + 1)`
(1-based periods; `w 0` is unused). -/
def IsThompsonRun {Ω Θ X Y W : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (P : Measure Ω) (θ : Ω → Θ) (w : ℕ → Ω → W) (g : X → Θ → W → Y) (r : Y → ℝ)
    (f : Θ → X) (θhat : ℕ → Ω → Θ) (xs : ℕ → Ω → X) : Prop :=
  Measurable f ∧
  (∀ (ϑ : Θ) (x : X), meanReward P w g r x ϑ ≤ meanReward P w g r (f ϑ) ϑ) ∧
  (∀ t, 1 ≤ t → Measurable (θhat t) ∧ xs t = fun ω => f (θhat t ω)) ∧
  (∀ t, 1 ≤ t → ∀ A : Set Θ, MeasurableSet A →
    P[(θhat t ⁻¹' A).indicator (fun _ => (1 : ℝ)) | history g θ w xs t]
      =ᵐ[P] P[(θ ⁻¹' A).indicator (fun _ => (1 : ℝ)) | history g θ w xs t]) ∧
  (∀ t, 1 ≤ t → ∀ (A : Set Θ) (C : Set (Θ × (ℕ → W))), MeasurableSet A → MeasurableSet C →
    P[(θhat t ⁻¹' A).indicator (fun _ => (1 : ℝ)) *
        ((fun ω => (θ ω, fun i : ℕ => w (i + 1) ω)) ⁻¹' C).indicator (fun _ => (1 : ℝ))
        | history g θ w xs t]
      =ᵐ[P] P[(θhat t ⁻¹' A).indicator (fun _ => (1 : ℝ)) | history g θ w xs t] *
        P[((fun ω => (θ ω, fun i : ℕ => w (i + 1) ω)) ⁻¹' C).indicator (fun _ => (1 : ℝ))
          | history g θ w xs t])

end ThompsonTutorial.Regret


