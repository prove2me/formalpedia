-- Prove2me | Definitions.Def_LNChannels_Exact_alphaMinus
-- name    : LNChannels_Exact_alphaMinus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:23.263981+00:00
-- url     : https://prove2.me/theorems/023488dc-3266-47f6-a93f-2f500e684671
-- title:
--   (4), p. 6 — the smaller root $\alpha_-$ of the characteristic equation
-- statement:
--   Let $\lambda_1,\lambda_2$ be the payment rates of a two-node payment channel and $r$ the continuously compounded discount rate. The **smaller root** of the characteristic equation $\lambda_2\alpha^2-(\lambda_1+\lambda_2+r)\alpha+\lambda_1=0$ is
--
--   $$\alpha_-=\frac{\lambda_1+\lambda_2+r-\sqrt{(\lambda_2-\lambda_1)^2+r^2+2r(\lambda_2+\lambda_1)}}{2\lambda_2}.$$
--
--   For $\lambda_1,\lambda_2,r>0$ one has $0<\alpha_-<1$. Together with $\alpha_+$ it gives the general solution of the first-step equation (15) and appears in the closed form (3) of the cost of a bidirectional channel.
--
--   **Formalization Note** The rates are written `lam₁`, `lam₂` because `λ` is a Lean keyword. The definition is a total function of three reals; it is the paper's root only when $\lambda_2>0$, and every theorem using it assumes $\lambda_2>0$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 6 (PDF p. 7), Theorem 1, equation (4)

import Mathlib

set_option autoImplicit false

namespace LNChannels.Exact

/-- The smaller root `α₋` of `λ₂ α² − (λ₁ + λ₂ + r) α + λ₁ = 0`, equation (4), p. 6. -/
noncomputable def alphaMinus (lam₁ lam₂ r : ℝ) : ℝ :=
  (lam₁ + lam₂ + r - Real.sqrt ((lam₂ - lam₁) ^ 2 + r ^ 2 + 2 * r * (lam₂ + lam₁))) / (2 * lam₂)

end LNChannels.Exact


