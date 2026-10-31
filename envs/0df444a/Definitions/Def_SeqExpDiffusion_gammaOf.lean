-- Prove2me | Definitions.Def_SeqExpDiffusion_gammaOf
-- name    : SeqExpDiffusion_gammaOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:57.632457+00:00
-- url     : https://prove2.me/theorems/f11902a8-8ea5-493a-b336-d5067c06c2ac
-- title:
--   The exponent $\gamma=(1+\sqrt{1+8r/\tilde\sigma^2})/2$
-- statement:
--   For a discount rate $r$ and volatility $\tilde\sigma$,
--
--   $$\gamma:=\frac{1+\sqrt{1+8r/\tilde\sigma^2}}{2}.$$
--
--   It is the larger root of $\tfrac{\tilde\sigma^2}{2}\gamma(\gamma-1)=r$, and it is the exponent of the closed-form solutions (16) and (18).
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, display (16), p.19; Proposition 5, p.20

import Mathlib

namespace SeqExpDiffusion

/-- The exponent `γ := (1 + √(1 + 8r/σ̃²))/2` of (16), Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, display (16), p.19, and
Proposition 5, p.20. -/
noncomputable def gammaOf (r σ : ℝ) : ℝ := (1 + Real.sqrt (1 + 8 * r / σ ^ 2)) / 2

end SeqExpDiffusion


