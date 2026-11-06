-- Prove2me | Definitions.Def_FourierRankQLB_rhoPlus
-- name    : FourierRankQLB_rhoPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:13.73263+00:00
-- url     : https://prove2.me/theorems/65d65aee-e931-4d01-b4d7-059bdc36cfa5
-- title:
--   The eigenangle density $\rho^+_N$
-- statement:
--   The function
--   $$
--   \rho^+_N(\theta)=\frac1\pi+\frac2\pi\sum_{j=1}^{N-1}\cos^2(j\theta),
--   $$
--   the expected density of the positive eigenangles under $\mu_{2N,+}$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 3.7, p.21

import Mathlib

namespace FourierRankQLB

/-- The density `ρ⁺_N(θ) = 1/π + (2/π) ∑_{j=1}^{N-1} cos²(jθ)`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 3.7, p. 21. -/
noncomputable def rhoPlus (N : ℕ) (θ : ℝ) : ℝ :=
  1 / Real.pi + 2 / Real.pi * ∑ j ∈ Finset.Icc 1 (N - 1), Real.cos (j * θ) ^ 2

end FourierRankQLB


