-- Prove2me | Definitions.Def_LNChannels_Exact_alphaPlus
-- name    : LNChannels_Exact_alphaPlus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:19.770301+00:00
-- url     : https://prove2.me/theorems/3b87e642-ed3b-4819-8837-279926079bbf
-- title:
--   (4), p. 6 — the larger root $\alpha_+$ of the characteristic equation
-- statement:
--   Let $\lambda_1,\lambda_2$ be the payment rates of a two-node payment channel and $r$ the continuously compounded discount rate. The **larger root** of the characteristic equation $\lambda_2\alpha^2-(\lambda_1+\lambda_2+r)\alpha+\lambda_1=0$ is
--
--   $$\alpha_+=\frac{\lambda_1+\lambda_2+r+\sqrt{(\lambda_2-\lambda_1)^2+r^2+2r(\lambda_2+\lambda_1)}}{2\lambda_2}.$$
--
--   Together with $\alpha_-$ it gives the general solution of the first-step equation (15) for the expected discounted cost of a bidirectional channel, and it appears in the closed form (3) of that cost.
--
--   **Formalization Note** The rates are written `lam₁`, `lam₂` because `λ` is a Lean keyword. The definition is a total function of three reals; it is the paper's root only when $\lambda_2>0$ (for $\lambda_1,\lambda_2,r>0$ one has $\alpha_+>1$), and every theorem using it assumes $\lambda_2>0$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 6 (PDF p. 7), Theorem 1, equation (4)

import Mathlib

set_option autoImplicit false

namespace LNChannels.Exact

/-- The larger root `α₊` of `λ₂ α² − (λ₁ + λ₂ + r) α + λ₁ = 0`, equation (4), p. 6. -/
noncomputable def alphaPlus (lam₁ lam₂ r : ℝ) : ℝ :=
  (lam₁ + lam₂ + r + Real.sqrt ((lam₂ - lam₁) ^ 2 + r ^ 2 + 2 * r * (lam₂ + lam₁))) / (2 * lam₂)

end LNChannels.Exact


