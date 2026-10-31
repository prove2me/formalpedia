-- Prove2me | Definitions.Def_SeqExpDiffusion_contValue
-- name    : SeqExpDiffusion_contValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:59.654982+00:00
-- url     : https://prove2.me/theorems/52ba7ade-8247-4906-8ee7-4eab0701d051
-- title:
--   The continuation-region solution $C^0(1-\delta)^\gamma\delta^{1-\gamma}+C^1(1-\delta)^{1-\gamma}\delta^\gamma$
-- statement:
--   For an exponent $\gamma$ and constants $C^0,C^1$, the function
--
--   $$u(\delta)=C^0\,(1-\delta)^{\gamma}\,\delta^{1-\gamma}+C^1\,(1-\delta)^{1-\gamma}\,\delta^{\gamma}=C^0\frac{(1-\delta)^\gamma}{\delta^{\gamma-1}}+C^1\frac{\delta^\gamma}{(1-\delta)^{\gamma-1}},\qquad\delta\in(0,1).$$
--
--   With $\gamma$ as in (16) these are all solutions of $\mathcal Hu=0$ on subintervals of $(0,1)$; the value of a two-action problem has this form in its continuation region.
--
--   **Formalization Note** Powers are real powers; the function is used only for $\delta\in(0,1)$.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, displays (16), p.19, and (18), p.20

import Mathlib

namespace SeqExpDiffusion

/-- The continuation-region solution
`C⁰ (1 − δ)^γ δ^{1−γ} + C¹ (1 − δ)^{1−γ} δ^γ = C⁰ (1 − δ)^γ / δ^{γ−1} + C¹ δ^γ / (1 − δ)^{γ−1}`,
Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, displays (16), p.19, and (18), p.20.

**Formalization Note** Powers are `Real.rpow`; the formula is used only for `δ ∈ (0, 1)`, where both
bases are positive. -/
noncomputable def contValue (γ C₀ C₁ δ : ℝ) : ℝ :=
  C₀ * (1 - δ) ^ γ * δ ^ (1 - γ) + C₁ * (1 - δ) ^ (1 - γ) * δ ^ γ

end SeqExpDiffusion


