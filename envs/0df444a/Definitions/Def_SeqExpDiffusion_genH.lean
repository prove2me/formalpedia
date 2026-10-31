-- Prove2me | Definitions.Def_SeqExpDiffusion_genH
-- name    : SeqExpDiffusion_genH
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:54.28572+00:00
-- url     : https://prove2.me/theorems/53ae1352-0709-4cda-954a-218f29499271
-- title:
--   The operator $\mathcal Hf=\tfrac12(\tilde\sigma\delta(1-\delta))^2f''-rf$ (corrected: squared volatility)
-- statement:
--   For $f\in\widehat{\mathcal C}^2$, the operator
--
--   $$\mathcal Hf(\delta):=\tfrac12\big(\tilde\sigma\,\delta(1-\delta)\big)^2f''(\delta)-r\,f(\delta),\qquad\delta\in[0,1]\setminus N_f,$$
--
--   is the generator of the belief diffusion (12) minus the discount term. It enters the quasi-variational inequalities (15).
--
--   **Formalization Note** The page prints $\tfrac12\tilde\sigma\,\delta(1-\delta)f''(\delta)-rf(\delta)$, without the square. That is not the generator of (12), and it contradicts the paper's own ODE above (16) (p.19), the proof of Proposition 5 (p.50) and the generator in the proof of Corollary 2 (p.52), all of which have $(\tilde\sigma\delta(1-\delta))^2/2$. With the printed operator the functions (16) would not solve $\mathcal Hf=0$. The second derivative is a derivative within $[0,1]$; it is meaningful only where it exists, which is how the QVI uses it.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, display (14), p.18 (corrected); ODE p.19; proofs pp.50, 52

import Mathlib

namespace SeqExpDiffusion

/-- The operator `ℋf(δ) := ½ (σ̃ δ (1 − δ))² f″(δ) − r f(δ)` on `Ĉ²`, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, display (14),
p.18 (corrected: squared volatility).

**Formalization Note** The page prints `½ σ̃ δ (1 − δ) f″(δ) − r f(δ)`, without the square. That
operator is not the generator of (12), and it contradicts the ODE above (16) on p.19, the proof of
Proposition 5 on p.50 and the generator in the proof of Corollary 2 on p.52, which all have
`(σ̃ δ (1 − δ))²/2`; with it, (16) would not solve `ℋf = 0` (for `σ̃ = 2`, `r = 1`, the ratio
`δ(1 − δ) φ₁″/φ₁` of `φ₁ = (1 − δ)^{1−γ} δ^γ` is `2.38` at `δ = 0.3` and `2.08` at `δ = 0.6`).
The second derivative is `derivWithin (derivWithin f [0, 1]) [0, 1]`; it is meaningful only where
it exists, which is how `SolvesQVI` uses it. -/
noncomputable def genH (r σ : ℝ) (f : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (σ * δ * (1 - δ)) ^ 2 / 2 *
      derivWithin (derivWithin f (Set.Icc 0 1)) (Set.Icc 0 1) δ - r * f δ

end SeqExpDiffusion


