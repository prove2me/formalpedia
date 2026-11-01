-- Prove2me | Definitions.Def_MarkovSA_moreauM
-- name    : MarkovSA_moreauM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:23.28172+00:00
-- url     : https://prove2.me/theorems/86669a5b-634c-4b91-a5bf-66e8bac990c5
-- title:
--   Generalized Moreau envelope $M(x)=\min_u\{\tfrac12\|u\|_c^2+\tfrac1\theta g(x-u)\}$
-- statement:
--   With $f(u)=\frac12\|u\|_c^2$ and $g(v)=\frac12\|v\|_s^2$, the **generalized Moreau envelope** of $f$ with respect to $g$ is
--
--   $$
--   M(x)=M_f^{\theta,g}(x)=\min_{u\in E}\Big\{f(u)+\frac1\theta g(x-u)\Big\}.
--   $$
--
--   It is the Lyapunov function of the proof: it is smooth with respect to $\|\cdot\|_s$ although $\|\cdot\|_c^2$ may not be.
--
--   **Formalization Note** Written as an infimum of a nonnegative objective; the minimum is attained, so the value is the paper's.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §A.1.1, p.25

import Mathlib

namespace MarkovSA

/-- The **generalized Moreau envelope** `M(x) = M_f^{θ,g}(x) = min_u { f(u) + (1/θ) g(x − u) }` with
`f(u) = ½‖u‖_c²` and `g(v) = ½‖v‖_s²` (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §A.1.1, p.25), the Lyapunov function of the proof.

**Formalization Note.** Written as an infimum (the objective is nonnegative, so the infimum is a real number;
it is attained, so it is the paper's minimum). -/
noncomputable def moreauM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (s : E → ℝ) (θ : ℝ) (x : E) : ℝ :=
  ⨅ u : E, ((1 / 2 : ℝ) * ‖u‖ ^ 2 + 1 / θ * ((1 / 2 : ℝ) * s (x - u) ^ 2))

end MarkovSA


