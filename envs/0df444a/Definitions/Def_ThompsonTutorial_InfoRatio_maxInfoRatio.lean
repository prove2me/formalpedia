-- Prove2me | Definitions.Def_ThompsonTutorial_InfoRatio_maxInfoRatio
-- name    : ThompsonTutorial_InfoRatio_maxInfoRatio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:11:40.85748+00:00
-- url     : https://prove2.me/theorems/f52944bb-ae82-4bed-8e59-070f89f0f6d8
-- title:
--   Maximal information ratio $\bar\Gamma=\max_{1\le t\le T}\Gamma_t$
-- statement:
--   For a horizon $T$, the **maximal information ratio** is
--   $$
--   \bar\Gamma\;=\;\max_{t\in\{1,\dots,T\}}\Gamma_t\;\in[0,\infty],
--   $$
--   where $\Gamma_t$ is the information ratio (8.7). It is the constant in front of the entropy in the regret bound (8.8).
--
--   **Formalization Note** A maximum in `ℝ≥0∞` over `Finset.Icc 1 T`; for $T=0$ it is $0$.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2, p. 76 (PDF p. 79), after (8.8): "where Γ̄ = max_{t∈{1,...,T}} Γt"

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_infoRatio
open MeasureTheory
open scoped ENNReal

namespace ThompsonTutorial.InfoRatio

/-- **The maximal information ratio `Γ̄ = max_{t ∈ {1,…,T}} Γ_t`.**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2, p. 76 (PDF p. 79), after (8.8): "where Γ̄ = max_{t∈{1,...,T}} Γt."

`maxInfoRatio P μ θ xstar x y T = max_{1 ≤ t ≤ T} infoRatio P μ θ xstar x y t`.

**Formalization Note.** A `Finset.sup` in `ℝ≥0∞`; for `T = 0` the index set is empty and the value
is `0`. -/
noncomputable def maxInfoRatio {Ω X Y Θ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : X → Θ → ℝ) (θ : Ω → Θ) (xstar : Ω → X)
    (x : ℕ → Ω → X) (y : ℕ → Ω → Y) (T : ℕ) : ℝ≥0∞ :=
  (Finset.Icc 1 T).sup (fun t => infoRatio P μ θ xstar x y t)

end ThompsonTutorial.InfoRatio


