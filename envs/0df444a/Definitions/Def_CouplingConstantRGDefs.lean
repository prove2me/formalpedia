-- Prove2me | Definitions.Def_CouplingConstantRGDefs
-- name    : CouplingConstantRGDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-03T13:49:40.804395+00:00
-- url     : https://prove2.me/theorems/0d3ec902-9791-48bf-9721-0d1dec328b4f
-- title:
--   Beta function in the energy scale $\beta(g)=\mu\,\partial g/\partial\mu$ and one-loop running in $\mu$
-- statement:
--   This file fixes the two objects in which the mission is stated, both written in the energy scale $\mu$ itself rather than in $t = \ln\mu$.
--
--   **1. The beta function in the energy scale.** For a coupling $g : \mathbb{R} \to \mathbb{R}$ regarded as a function of the energy scale, its beta function is
--   $$\beta(g)(\mu) \;=\; \mu \cdot \frac{d g}{d\mu}(\mu),$$
--   the quantity the source uses to define the running of a coupling. It is a function of $\mu$, defined for every real $\mu$ and every $g$; at a scale where $g$ has no derivative the underlying derivative operator returns $0$, so statements below restrict to scales where differentiability is assumed.
--
--   **2. One-loop running in $\mu$.** For a one-loop coefficient $b \in \mathbb{R}$, a coupling $\alpha$ and a set $S$ of scales, the predicate "$\alpha$ is one-loop running with coefficient $b$ on $S$" asserts that at every $\mu \in S$ the coupling is differentiable with
--   $$\frac{d\alpha}{d\mu}(\mu) \;=\; \frac{b\,\alpha(\mu)^2}{\mu}, \qquad\text{equivalently}\qquad \mu\,\frac{d\alpha}{d\mu}(\mu) = b\,\alpha(\mu)^2 .$$
--   The sign of $b$ distinguishes the two regimes the source describes: $b < 0$ is the asymptotically free case of QCD, $b > 0$ the case the source attributes to QED.
--
--   These two objects are the model on which every statement of the mission rests. The explicit one-loop strong coupling $\alpha(Q) = 1/(\beta_0 \ln(Q^2/\Lambda^2))$ is not redefined here: the mission reuses the published platform definition for it.
--
--   **Formalization Note** The derivative in the one-loop predicate is the two-sided derivative at each point of $S$, so the predicate also constrains the coupling in a neighbourhood of an endpoint of an interval; the division by $\mu$ is harmless on the sets of positive scales used throughout.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 (the uploaded PDF) - sections "Running coupling", "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale".

import Mathlib

namespace CouplingConstantRG

/-- The beta function of a running coupling `g` in the energy scale `μ`:
`β(g)(μ) = μ * ∂g/∂μ`. -/
noncomputable def betaFunctionMu (g : ℝ → ℝ) (μ : ℝ) : ℝ := μ * deriv g μ

/-- `IsMuRunning b α s` says that on the set of energy scales `s` the coupling `α`
obeys the one-loop renormalization-group equation written in the energy scale `μ`,
`μ * dα/dμ = b * α ^ 2`, i.e. `dα/dμ = b * α ^ 2 / μ`. -/
def IsMuRunning (b : ℝ) (α : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ μ ∈ s, HasDerivAt α (b * α μ ^ 2 / μ) μ

end CouplingConstantRG


