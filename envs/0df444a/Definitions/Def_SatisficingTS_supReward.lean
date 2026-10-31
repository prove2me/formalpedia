-- Prove2me | Definitions.Def_SatisficingTS_supReward
-- name    : SatisficingTS_supReward
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:00.012601+00:00
-- url     : https://prove2.me/theorems/7ec323ee-6e90-4772-b5e5-e8337e86231e
-- title:
--   Supremal reward $R^*=\sup_a\mu(a,\theta)$
-- statement:
--   The supremal reward is
--   $$
--   R^*=\sup_{a\in\mathcal A}\mu(a,\theta),
--   $$
--   a random variable through $\theta$, where $\mu(a,\theta)=\mathbb E[R(g(a,\theta,W_t))\mid\theta]$ is the expected reward of action $a$. It is the benchmark of the ordinary regret, and $R^*-D$ the benchmark of the satisficing regret.
--
--   **Formalization Note** $\mu(a,\theta)$ is the published `ThompsonTutorial.InfoRatio.meanReward` with the law of $W_0$ as disturbance law, $\int R(g(a,\theta,w))\,\mathbb P_{W_0}(dw)$, a version of the conditional expectation because the $W_t$ are identically distributed and independent of $\theta$. $\mathrm{supReward}(\theta)$ is a real supremum; Lean returns $0$ for a set that is not bounded above, so theorems assume that $a\mapsto\mu(a,\theta)$ is bounded above almost surely.
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, §2, p.5 ("Let R∗ = supa∈A µ(a, θ) denote the supremal reward")

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_meanReward
open MeasureTheory ThompsonTutorial.InfoRatio

namespace SatisficingTS

/-- **The supremal reward `R* = sup_{a∈A} µ(a, θ)`** (Russo & Van Roy, *Satisficing in
Time-Sensitive Bandit Learning*, arXiv:1803.02855v2, §2, p.5): "Let R∗ = supa∈A µ(a, θ) denote the
supremal reward".

`supReward P W g R th = ⨆ a, µ(a, th)`, where `µ(a, th)` is the published
`ThompsonTutorial.InfoRatio.meanReward g R (P.map (W 0)) a th = ∫ R(g(a, th, w)) d(law of W_0)(w)`,
a version of the paper's `µ(a, θ) = E[R(g(a, θ, Wt)) | θ]` (p.5) because the disturbances are
identically distributed and independent of `θ`. The paper's random variable `R*` is
`supReward P W g R (θ ω)`.

**Formalization Note.** A real supremum: Lean's `⨆` of a set that is not bounded above is `0`,
so every theorem using `R*` assumes `BddAbove` (almost surely in `θ`). -/
noncomputable def supReward {Ω Θ 𝒲 𝒜 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒲]
    (P : Measure Ω) (W : ℕ → Ω → 𝒲) (g : 𝒜 → Θ → 𝒲 → 𝒴) (R : 𝒴 → ℝ) (th : Θ) : ℝ :=
  ⨆ a, meanReward g R (P.map (W 0)) a th

end SatisficingTS


