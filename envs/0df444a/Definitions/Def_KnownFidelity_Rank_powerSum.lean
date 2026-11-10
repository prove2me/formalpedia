-- Prove2me | Definitions.Def_KnownFidelity_Rank_powerSum
-- name    : KnownFidelity_Rank_powerSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:50.22278+00:00
-- url     : https://prove2.me/theorems/51a58535-64ad-4459-97b0-fa43a7cef44c
-- title:
--   Power sums $u_{b,k}=\sum_i (a^{(b)}_i)^k$
-- statement:
--   For a vector $a\in\mathbb R^r$ and $k\in\mathbb N$, the $k$-th power sum is
--
--   $$p_k(a)=\sum_{i=1}^r a_i^k .$$
--
--   The moment-matching condition (29) of Proposition 5.2 equates the power sums of two vectors for $1\le k\le K$, and $u_{b,k}=p_k(a^{(b)})$ in §5.5.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §5.5 (unnumbered display), p. 20 (PDF p. 22); Eq. (29), p. 12 (PDF p. 14)

import Mathlib

namespace KnownFidelity.Rank

/-- **Power sums `u_{b,k} = p_k(a^{(b)}) = Σ_i (a^{(b)}_i)^k`.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §5.5 (unnumbered display), printed p. 20 (PDF p. 22): "Let
u_{b,k} = p_k(a^{(b)}) = Σ_i (a^{(b)}_i)^k", and Eq. (29), printed p. 12 (PDF p. 14).

**Formalization Note.** For a vector `a : Fin r → ℝ` and `k : ℕ`; `powerSum a 0 = r`. -/
def powerSum {r : ℕ} (a : Fin r → ℝ) (k : ℕ) : ℝ :=
  ∑ i, a i ^ k

end KnownFidelity.Rank


