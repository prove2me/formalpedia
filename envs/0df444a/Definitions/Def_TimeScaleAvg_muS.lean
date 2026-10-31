-- Prove2me | Definitions.Def_TimeScaleAvg_muS
-- name    : TimeScaleAvg_muS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:53.880994+00:00
-- url     : https://prove2.me/theorems/bd7bca5d-445a-4e09-8729-ee9f89d79b76
-- title:
--   The averaging measure $\mu_s$ on $[s_0,s]$
-- statement:
--   For $0<s_0\le s$ and $\alpha>1$, the measure on $[s_0,s]$ used to average the trajectory is
--
--   $$
--   \mu_s=\frac{s_0^{\alpha-1}}{s^{\alpha-1}}\,\delta_{s_0}+(\alpha-1)\frac{u^{\alpha-2}}{s^{\alpha-1}}\,du,
--   $$
--
--   where $\delta_{s_0}$ is the Dirac measure at $s_0$. It is the probability measure with respect to which $x$ is an average of $y$, up to a small perturbation.
--
--   **Formalization Note** $\mu_s$ is a measure on $\mathbb R$: a weighted Dirac mass plus Lebesgue measure restricted to $[s_0,s]$ with the density shown. The exponents are real, on positive bases. An integral $\int_{s_0}^s\cdot\,d\mu_s$ is taken against the whole measure, the atom at $s_0$ included.
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, p.7

import Mathlib

open MeasureTheory

namespace TimeScaleAvg

/-- The averaging measure on `[s₀, s]`,
`μ_s = (s₀^{α-1}/s^{α-1}) δ_{s₀} + (α-1) (u^{α-2}/s^{α-1}) du`
(Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.7), as a measure on `ℝ`: the Dirac mass at `s₀` with
the weight shown, plus Lebesgue measure restricted to `[s₀, s]` with the density shown.

**Formalization Note.** Exponents are real (`Real.rpow`), used on positive bases: the paper has
`s ≥ s₀ > 0`. Below that range the value of `muS` carries no meaning and no statement uses it. An
integral `∫_{s₀}^{s} … dμ_s(u)` of the paper is the integral against this whole measure, atom at
`s₀` included. -/
noncomputable def muS (α s₀ s : ℝ) : Measure ℝ :=
  ENNReal.ofReal (s₀ ^ (α - 1) / s ^ (α - 1)) • Measure.dirac s₀ +
    (volume.restrict (Set.Icc s₀ s)).withDensity
      (fun u => ENNReal.ofReal ((α - 1) * (u ^ (α - 2) / s ^ (α - 1))))

end TimeScaleAvg


