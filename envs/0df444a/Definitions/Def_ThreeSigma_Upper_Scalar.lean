-- Prove2me | Definitions.Def_ThreeSigma_Upper_Scalar
-- name    : ThreeSigma_Upper_Scalar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:19.205891+00:00
-- url     : https://prove2.me/theorems/1160dbac-f2a7-4d5e-9588-b00aee9182fc
-- title:
--   Scalar potential φ, derivative-defined ψ, and threshold c
-- statement:
--   For positive real $t$, define
--   $$\phi(t)=\frac{5}{\sinh(t^2/3)},\qquad \psi(t)=-t\phi'(t)-2\phi(t),\qquad c=\sqrt{3\operatorname{arsinh}(10)}.$$
--   These are the scalar functions and fixed threshold used in the upper bound. The derivative in $\psi$ is the genuine derivative of the displayed formula.
--
--   **Formalization Note** This module supplies the real smooth formula only. It extends to all real arguments by total division, so its value at zero is $0$. The source's extended potential has $\phi(0)=+\infty$; no boundary potential is defined here. Every theorem about $\phi$ restricts the argument to $(0,\infty)$ or takes its right limit at zero.
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), §3, pp. 5–6, Figure 1, and Appendix C, pp. 14–15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf

import Mathlib

namespace ThreeSigma.Upper

/-- The real smooth formula for the paper's φ, used only on positive arguments.
At zero the real extension is 0, not the extended potential's +∞. -/
noncomputable def phi (t : ℝ) : ℝ := 5 / Real.sinh (t ^ 2 / 3)

/-- ψ is computed from the genuine derivative of φ (p. 6). -/
noncomputable def psi (t : ℝ) : ℝ := -t * deriv phi t - 2 * phi t

/-- Figure 1's threshold, not an implicitly specified root. -/
noncomputable def c : ℝ := Real.sqrt (3 * Real.arsinh 10)

end ThreeSigma.Upper


