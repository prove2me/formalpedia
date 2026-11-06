-- Prove2me | Definitions.Def_FourierRankQLB_rhoMinus
-- name    : FourierRankQLB_rhoMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:20.083212+00:00
-- url     : https://prove2.me/theorems/a108ec53-3f0f-4050-afa4-50f60e88c9d3
-- title:
--   The eigenangle density $\rho^-_N$
-- statement:
--   The function
--   $$
--   \rho^-_N(\theta)=\frac2\pi\sum_{j=1}^{N-1}\sin^2(j\theta),
--   $$
--   the expected density of the non-forced positive eigenangles under $\mu_{2N,-}$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 3.7, p.21

import Mathlib

namespace FourierRankQLB

/-- The density `ρ⁻_N(θ) = (2/π) ∑_{j=1}^{N-1} sin²(jθ)`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 3.7, p. 21. -/
noncomputable def rhoMinus (N : ℕ) (θ : ℝ) : ℝ :=
  2 / Real.pi * ∑ j ∈ Finset.Icc 1 (N - 1), Real.sin (j * θ) ^ 2

end FourierRankQLB


