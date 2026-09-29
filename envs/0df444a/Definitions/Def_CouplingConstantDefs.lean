-- Prove2me | Definitions.Def_CouplingConstantDefs
-- name    : CouplingConstantDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T20:48:50.052309+00:00
-- url     : https://prove2.me/theorems/5bc0f1a4-c711-4815-8111-492cb4014df4
-- title:
--   One-loop beta function, one-loop RG flow, and the one-loop coupling $\alpha(Q)=1/(\beta_0\log(Q^2/\Lambda^2))$
-- statement:
--   This file fixes the three objects the mission is stated in terms of.
--
--   **1. The one-loop beta function.** For a real coefficient $b$ and a real coupling $g$,
--   $$\beta_b(g) \;=\; b\,g^{3}.$$
--   This is the one-loop truncation of the beta function of a single coupling; the coefficient $b$ is theory- and scheme-dependent, and is negative for a non-abelian gauge theory such as QCD and positive for QED.
--
--   **2. One-loop running.** Let $t = \log\mu$ denote the logarithm of the energy scale and let $g : \mathbb{R}\to\mathbb{R}$ be a coupling regarded as a function of $t$. For a set of scales $S \subseteq \mathbb{R}$ we say that $g$ *runs at one loop with coefficient $b$ on $S$* when
--   $$\frac{dg}{dt}(t) \;=\; \mu\frac{dg}{d\mu} \;=\; \beta_b\big(g(t)\big) \;=\; b\,g(t)^{3} \qquad\text{for every } t \in S,$$
--   the derivative being the ordinary (two-sided) derivative of $g$ at $t$.
--
--   **3. The one-loop QCD coupling.** For a one-loop coefficient $\beta_0$, a QCD scale $\Lambda$ and a process energy $Q$,
--   $$\alpha(Q) \;=\; \frac{1}{\beta_0\,\log\!\big(Q^{2}/\Lambda^{2}\big)},$$
--   the closed form quoted in the source for the strong coupling in the asymptotically free regime.
--
--   These three notions are the vocabulary of the mission: the goal theorem and every milestone is phrased using them, so that the prose and the formal statements describe the same objects.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 — sections "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale"

import Mathlib

namespace CouplingConstant

/-- The one-loop beta function `β(g) = b * g ^ 3` for a single coupling `g`,
with scheme-dependent one-loop coefficient `b`. -/
noncomputable def betaOneLoop (b g : ℝ) : ℝ := b * g ^ 3

/-- `IsOneLoopRunning b g s` says that on the set of scales `s` the coupling `g`,
viewed as a function of `t = Real.log μ`, obeys the renormalization-group equation
`μ * dg/dμ = dg/dt = β(g) = b * g ^ 3`. -/
def IsOneLoopRunning (b : ℝ) (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt g (betaOneLoop b (g t)) t

/-- The one-loop QCD running coupling
`α(Q) = 1 / (β₀ * log (Q ^ 2 / Λ ^ 2))`,
with one-loop coefficient `β₀` and QCD scale `Λ`. -/
noncomputable def alphaOneLoop (beta0 Lam Q : ℝ) : ℝ :=
  1 / (beta0 * Real.log (Q ^ 2 / Lam ^ 2))

end CouplingConstant


