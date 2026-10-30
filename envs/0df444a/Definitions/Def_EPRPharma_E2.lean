-- Prove2me | Definitions.Def_EPRPharma_E2
-- name    : EPRPharma_E2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:04:57.787654+00:00
-- url     : https://prove2.me/theorems/eb5d186b-18ce-457b-aca5-ca40067b24cc
-- title:
--   Joint expectation $E_{\theta_n,\theta_u}$ over need and usage
-- statement:
--   The quantity $\theta_u$ the patient prefers to use is uniformly distributed on $[0,1]$ and independent of the need $\theta_n$, which is also uniform on $[0,1]$. For a function $g$ of both,
--
--   $$E_{\theta_n,\theta_u}[g]=\int_0^1\!\!\int_0^1 g(\theta_n,\theta_u)\,d\theta_u\,d\theta_n .$$
--
--   **Formalization Note** Encoded as an iterated interval integral over $[0,1]^2$.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.1, p. 11 (unnumbered)

import Mathlib

namespace EPRPharma

/-- **Joint expectation over the patient's need θ_n and preferred usage θ_u.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.1, p. 11: "θ_u is
uniformly distributed on [0,1] and is independent of θ_n", with θ_n uniform on [0, 1].
`E2 g` is E_{θ_n,θ_u}[g(θ_n, θ_u)] = ∫₀¹ ∫₀¹ g(θ_n, θ_u) dθ_u dθ_n.

**Formalization Note.** Independence of two uniforms is encoded as the iterated interval integral
over [0, 1]². -/
noncomputable def E2 (g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ θn in (0:ℝ)..1, ∫ θu in (0:ℝ)..1, g θn θu

end EPRPharma


