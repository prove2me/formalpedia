-- Prove2me | Definitions.Def_FoundationsRL_OnlineLearning_LogLossWeights
-- name    : FoundationsRL_OnlineLearning_LogLossWeights
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:18:26.111204+00:00
-- url     : https://prove2.me/theorems/cfd8f0e6-5b9c-4529-b45f-68676642e79f
-- title:
--   Exponential Weights for the log loss at $\eta=1$: likelihood, distribution, potential
-- statement:
--   Let $\mathcal F$ be a finite class of conditional densities $f(y\mid x)$. These are (1.23) and (1.26) at $\eta=1$ for the log loss, where the loss may be $+\infty$.
--
--   1. **Likelihood.** $\prod_{i=1}^t f(y^i\mid x^i)$, which is $\exp\{-\sum_{i=1}^t\ell_{\log}(f(x^i),y^i)\}$ with the convention $\exp(-\infty)=0$.
--   2. **Distribution.** $q^t(f)$ is the likelihood of the first $t-1$ rounds, normalized over $\mathcal F$, as in (1.27).
--   3. **Potential.** $\Phi^t_1=-\log\sum_{f\in\mathcal F}\prod_{i=1}^t f(y^i\mid x^i)$, with value $+\infty$ when every $f\in\mathcal F$ has likelihood $0$.
--
--   These make the log-loss analysis of the notes precise when some density vanishes on the data.
--
--   **Formalization Note** If every $f\in\mathcal F$ has likelihood $0$ on the past, the notes' formula reads $0/0$. Lean's value is $0$, the averaged density is then $0$, and the algorithm suffers $+\infty$. Every comparator has then already suffered $+\infty$, so no regret statement depends on this case.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (1.23), p. 15, (1.26)–(1.27), p. 16

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_Losses

namespace FoundationsRL.OnlineLearning

/-- **Likelihood of the first `t` rounds** `∏_{i=1}^t f(y^i | x^i)`. This is the weight
`exp{-∑_{i=1}^t ℓ_log(f(x^i), y^i)}` of (1.27), p. 16, arXiv:2312.16730v1, with the convention
`exp(-∞) = 0` for a zero density.

**Formalization Note.** The log loss can be `+∞`, so (1.23) at `η = 1` is written as this product
rather than through `ewWeight`, which needs a real-valued loss. The two agree when every density
involved is positive. -/
noncomputable def likelihood {X Y : Type*} (f : X → Y → ℝ) (x : ℕ → X) (y : ℕ → Y) (t : ℕ) : ℝ :=
  ∏ i ∈ Finset.range t, f (x i) (y i)

/-- **The Exponential Weights distribution for the log loss at `η = 1`**, (1.23) and (1.27), p. 16,
arXiv:2312.16730v1: `q^t(f) ∝ exp{-∑_{i=1}^{t-1} ℓ_log(f(x^i), y^i)}`.

**Formalization Note.** If every `f ∈ F` has likelihood `0` on the past, the notes' formula reads
`0/0`. Lean's value is `0`, so the averaged density is `0` and the algorithm then suffers `+∞` loss.
In that case every comparator has already suffered `+∞`, so no regret statement depends on it. -/
noncomputable def logDist {X Y : Type*} (F : Finset (X → Y → ℝ)) (x : ℕ → X) (y : ℕ → Y) (t : ℕ)
    (f : X → Y → ℝ) : ℝ :=
  likelihood f x y t / ∑ g ∈ F, likelihood g x y t

/-- **The potential for the log loss at `η = 1`**, (1.26), p. 16, arXiv:2312.16730v1:
`Φ^t_1 = -log ∑_{f ∈ F} exp{-∑_{i=1}^t ℓ_log(f(x^i), y^i)}`, with value `+∞` when every `f ∈ F`
has likelihood `0`. -/
noncomputable def logPotential {X Y : Type*} (F : Finset (X → Y → ℝ)) (x : ℕ → X) (y : ℕ → Y)
    (t : ℕ) : EReal :=
  negLog (∑ f ∈ F, likelihood f x y t)

end FoundationsRL.OnlineLearning


