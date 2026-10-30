-- Prove2me | Definitions.Def_EPRPharma_E1
-- name    : EPRPharma_E1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:04:41.494761+00:00
-- url     : https://prove2.me/theorems/6f90a505-a7d0-4b43-8808-ef3bbbdcce24
-- title:
--   Expectation $E_{\theta_n}$ over the patient's need
-- statement:
--   The patient's need $\theta_n$ is uniformly distributed on $[0,1]$. For a function $f$ of the need,
--
--   $$E_{\theta_n}[f]=\int_0^1 f(\theta_n)\,d\theta_n .$$
--
--   **Formalization Note** Encoded as an interval integral over $[0,1]$.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.1, pp. 8–9 (unnumbered)

import Mathlib

namespace EPRPharma

/-- **Expectation over the patient's need θ_n.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.1, pp. 8–9: the patient's need θ_n is
uniformly distributed on [0, 1]. `E1 f` is E_{θ_n}[f(θ_n)] = ∫₀¹ f(θ_n) dθ_n.

**Formalization Note.** Encoded as the interval integral over [0, 1]. Every integrand used in this
mission is bounded and piecewise affine on [0, 1], hence integrable. -/
noncomputable def E1 (f : ℝ → ℝ) : ℝ :=
  ∫ θn in (0:ℝ)..1, f θn

end EPRPharma


