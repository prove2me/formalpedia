-- Prove2me | Definitions.Def_FourierRankQLB_signAvg
-- name    : FourierRankQLB_signAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:15.551203+00:00
-- url     : https://prove2.me/theorems/fbce2277-cb65-4be3-914d-23813408ee83
-- title:
--   The average over a uniform sign vector
-- statement:
--   For $f:\{-1,+1\}^d\to\mathbb R$, the expectation over independent uniform signs,
--   $$
--   \mathbb E_\sigma f(\sigma)=2^{-d}\sum_{\sigma\in\{-1,+1\}^d}f(\sigma).
--   $$
--   A probability over $\sigma$ is the average of an indicator.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §4.3, p.28

import Mathlib
import Definitions.Def_FourierRankQLB_SignVec

namespace FourierRankQLB

/-- The expectation `E_σ f(σ) = 2^{-d} ∑_σ f(σ)` over a uniform sign vector.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §4.3, p. 28 ("`σ₁, …, σ_d` are independent and uniform on `{-1, +1}`").

**Formalization Note.** The uniform law on the finite set `{-1, +1}^d` is written as this finite
average, and a probability is the average of an indicator. -/
noncomputable def signAvg {d : ℕ} (f : SignVec d → ℝ) : ℝ := ((2 : ℝ) ^ d)⁻¹ * ∑ σ, f σ

end FourierRankQLB


