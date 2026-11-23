-- Prove2me | Definitions.Def_RiddledBasins_Uncertainty
-- name    : RiddledBasins_Uncertainty
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T20:33:06.965943+00:00
-- url     : https://prove2.me/theorems/f079e7a8-ec5f-4f8f-b4b1-2815547074a3
-- title:
--   Uncertainty fraction $f(\varepsilon)$ and scaling exponent $\phi$
-- statement:
--   This file defines the quantities the paper uses to measure how much predictability is lost at small scales.
--
--   For an initialization $\theta$ and a scale $\varepsilon>0$, the **$\varepsilon$-uncertainty fraction** is
--   $$f_\theta(\varepsilon)=\frac{l\big(B_\varepsilon(\theta)\cap\beta(A)^{c}\big)}{l\big(B_\varepsilon(\theta)\big)},$$
--   the probability that a uniformly random perturbation of magnitude $\varepsilon$ moves the initialization out of the basin of $A$; averaging over a sampling distribution $\mu$ of initializations gives the ensemble fraction $f(\varepsilon)=\int f_\theta(\varepsilon)\,d\mu(\theta)$. A **scaling exponent** $\phi$ for a quantity $f$ means
--   $$\lim_{\varepsilon\to0^{+}}\frac{f(\varepsilon)}{\varepsilon^{\phi}}=c\quad\text{for some }c>0,$$
--   which is the precise reading of the power law $f(\varepsilon)\propto\varepsilon^{\phi}$ used for the parameter-space uncertainty exponent and, with $f$ replaced by a functional similarity measure, for the functional uncertainty exponent.
--
--   The exponent is the paper's summary statistic for reproducibility: $\phi\approx0$ says that sharpening the initialization by many orders of magnitude barely reduces the chance of a different outcome.
--
--   **Formalization Note.** The ratio uses `ENNReal.toReal`; a ball has finite positive volume for $\varepsilon>0$, so the fraction is a real number in $[0,1]$, and it is $0$ at $\varepsilon\le0$ because `Metric.ball` is then empty. The exponent is defined through a limit of ratios rather than a logarithmic derivative, so no positivity assumption on $f$ is needed to state it.
-- source:
--   A. Ly & P. Gong, Fractal basin geometry and the limits to predictability and reproducibility in deep learning, Nature Machine Intelligence (2026), https://doi.org/10.1038/s42256-026-01336-3, PDF p. 5, eq. (5) and 'A limit to reproducibility'; PDF p. 4, Fig. 3e; PDF p. 10, Methods, 'Uncertainty exponent calculation'

import Mathlib
import Definitions.Def_RiddledBasins_Dynamics

open MeasureTheory Metric Set Filter Topology

namespace RiddledBasins

/-- The local `ε`-uncertainty fraction at `θ`: the probability that a uniformly random
perturbation of size `ε` leaves the basin of `A`. -/
noncomputable def uncertaintyFraction {d : ℕ} (Φ : Param d → Param d) (A : Set (Param d))
    (θ : Param d) (ε : ℝ) : ℝ :=
  (volume (Metric.ball θ ε ∩ (basin Φ A)ᶜ)).toReal / (volume (Metric.ball θ ε)).toReal

/-- The uncertainty fraction averaged over a sampling measure `μ` on parameter space. -/
noncomputable def avgUncertaintyFraction {d : ℕ} (Φ : Param d → Param d) (A : Set (Param d))
    (μ : Measure (Param d)) (ε : ℝ) : ℝ :=
  ∫ θ, uncertaintyFraction Φ A θ ε ∂μ

/-- Power-law scaling `f(ε) ∝ ε^φ` as `ε → 0+`, with a positive proportionality constant. -/
def HasScalingExponent (f : ℝ → ℝ) (φ : ℝ) : Prop :=
  ∃ c > 0, Filter.Tendsto (fun ε => f ε / Real.rpow ε φ) (nhdsWithin 0 (Set.Ioi 0)) (nhds c)

end RiddledBasins


