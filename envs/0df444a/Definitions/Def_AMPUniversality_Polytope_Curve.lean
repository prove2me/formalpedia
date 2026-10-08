-- Prove2me | Definitions.Def_AMPUniversality_Polytope_Curve
-- name    : AMPUniversality_Polytope_Curve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:50.908577+00:00
-- url     : https://prove2.me/theorems/c8977517-4a86-4ace-a853-b8967513d345
-- title:
--   Equations (1.2)–(1.3), pp. 4–5 — parametric weak-neighborliness boundary
-- statement:
--   Let $\phi$ and $\Phi$ be the density and distribution function of a standard normal random variable. The paper parameterizes its phase boundary by $\alpha>0$ through
--
--   $$f_\delta(\alpha)=\frac{2\phi(\alpha)}{\alpha+2(\phi(\alpha)-\alpha\Phi(-\alpha))},\qquad f_\rho(\alpha)=1-\frac{\alpha\Phi(-\alpha)}{\phi(\alpha)}.$$
--
--   The coordinate $f_\delta(\alpha)$ is the sampling ratio and $f_\rho(\alpha)$ is the corresponding weak-neighborliness ratio. Theorems use a positive parameter satisfying $f_\delta(\alpha)=\delta$, avoiding an inverse outside its proven domain.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, pp. 4–5, equations (1.2)–(1.3)

import Mathlib

set_option autoImplicit false

namespace AMPUniversality.Polytope

/-- Standard Gaussian density. -/
noncomputable def phi (x : ℝ) : ℝ := ProbabilityTheory.gaussianPDFReal 0 1 x

/-- Standard Gaussian cumulative distribution function. -/
noncomputable def Phi (x : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x

/-- The sampling ratio in the parametric boundary (1.2). -/
noncomputable def fδ (α : ℝ) : ℝ :=
  2 * phi α / (α + 2 * (phi α - α * Phi (-α)))

/-- The sparsity ratio in the parametric boundary (1.3). -/
noncomputable def fρ (α : ℝ) : ℝ :=
  1 - α * Phi (-α) / phi α

end AMPUniversality.Polytope


