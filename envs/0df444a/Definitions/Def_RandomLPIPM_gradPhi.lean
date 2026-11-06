-- Prove2me | Definitions.Def_RandomLPIPM_gradPhi
-- name    : RandomLPIPM_gradPhi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:39.094653+00:00
-- url     : https://prove2.me/theorems/8786f9dc-aaba-4980-a239-3f654a5fa073
-- title:
--   Gradient $\nabla\Phi_{x,\mu}(u)$
-- statement:
--   The gradient of $\Phi_{x,\mu}$ is
--   $$\nabla\Phi_{x,\mu}(u)_i=\frac{x_ic_i}{\mu}-1+\tilde d'(u_i),\qquad i\in[n].$$
--   The projected gradient $P_x\nabla\Phi_{x,\mu}(u)$ is the step direction and the stopping quantity of the inner loop of Algorithm 1.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (116), p.78; Algorithm 1, p.80

import Mathlib
import Definitions.Def_RandomLPIPM_dTildeDeriv

open Matrix

namespace RandomLPIPM

/-- **The gradient `∇Φ_{x,μ}(u)`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (116), p.78: differentiating
`Φ_{x,μ}(u) = (Xc/μ − 1)ᵀu + ∑ᵢ d̃(uᵢ)` gives `∇Φ_{x,μ}(u)ᵢ = xᵢcᵢ/μ − 1 + d̃′(uᵢ)`. -/
noncomputable def gradPhi {n : ℕ} (c x : Fin n → ℝ) (μ : ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i * c i / μ - 1 + dTildeDeriv (u i)

end RandomLPIPM


