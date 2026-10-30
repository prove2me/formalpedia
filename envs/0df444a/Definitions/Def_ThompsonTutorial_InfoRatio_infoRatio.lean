-- Prove2me | Definitions.Def_ThompsonTutorial_InfoRatio_infoRatio
-- name    : ThompsonTutorial_InfoRatio_infoRatio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:10:52.406898+00:00
-- url     : https://prove2.me/theorems/4ded2e9e-f191-419b-90b5-198941c6c8c2
-- title:
--   Information ratio $\Gamma_t$, (8.7)
-- statement:
--   In the online decision model, with optimal action $x^*$, actions $x_t$, outcomes $y_t$ and history $H_{t-1}=((x_1,y_1),\dots,(x_{t-1},y_{t-1}))$, the **information ratio** of period $t\ge1$ is
--   $$
--   \Gamma_t\;=\;\frac{\big(\mathbb E[\mu(x^*,\theta)-\mu(x_t,\theta)]\big)^2}{I\big(x^*;(x_t,y_t)\mid H_{t-1}\big)} .
--   $$
--   The numerator is the square of the expected single-period regret, and the denominator is the conditional mutual information between the optimal action and the observation of period $t$, the expected information gain. The ratio is the expected "cost" paid per unit of information acquired. This is the version of the tutorial (footnote 1), which integrates over histories; it is not the per-history ratio of Russo and Van Roy (2016).
--
--   **Formalization Note** The value is in $[0,\infty]$ (`ℝ≥0∞`): $a/0=+\infty$ for $a>0$, $0/0=0$, and $a/\infty=0$. It is used only for $t\in\{1,\dots,T\}$, where $t-1$ is the true predecessor. Information in nats.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2, p. 75 (PDF p. 78), (8.7) and footnote 1

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_ThompsonTutorial_InfoRatio_history
open MeasureTheory
open scoped ENNReal

namespace ThompsonTutorial.InfoRatio

/-- **The information ratio `Γ_t`, (8.7).**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2, p. 75 (PDF p. 78), (8.7):
"Γt = (E[μ(x∗, θ) − μ(xt, θ)])² / I(x∗; (xt, yt)|Ht−1). The numerator is the square of expected
single-period regret, while in the denominator, the conditional mutual information
I(x∗; (xt, yt)|Ht−1) between the uncertain optimal action x∗ and the impending observation
(xt, yt) measures expected information gain." Footnote 1: this version "integrates over h_t".

`infoRatio P μ θ xstar x y t = (E[μ(x*, θ) − μ(x_t, θ)])² / I(x*; (x_t, y_t) | H_{t−1})`, where
`H_{t−1} = ((x_1, y_1), …, (x_{t−1}, y_{t−1}))`. The numerator is the square of the
*unconditional* expected one-period regret; the denominator is the conditional mutual information
(averaged over histories) — not the per-history ratio of footnote 1.

**Formalization Note.** Value in `ℝ≥0∞`: the numerator is embedded by `ENNReal.ofReal`, and
`ℝ≥0∞` division gives `a / 0 = ⊤` for `a ≠ 0`, `0 / 0 = 0`, and `a / ⊤ = 0` for `a ≠ ⊤`. Used only
for `t ∈ {1, …, T}`, where `t − 1` is the true predecessor (natural-number subtraction is never
truncated there). Information in nats. -/
noncomputable def infoRatio {Ω X Y Θ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : X → Θ → ℝ) (θ : Ω → Θ) (xstar : Ω → X)
    (x : ℕ → Ω → X) (y : ℕ → Ω → Y) (t : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((∫ ω, (μ (xstar ω) (θ ω) - μ (x t ω) (θ ω)) ∂P) ^ 2) /
    condMutualInfo P xstar (fun ω => (x t ω, y t ω))
      (history (fun s ω => (x s ω, y s ω)) (t - 1))

end ThompsonTutorial.InfoRatio


