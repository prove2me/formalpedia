-- Prove2me | Definitions.Def_FourierEntropyApprox_Ka
-- name    : FourierEntropyApprox_Ka
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:32.459309+00:00
-- url     : https://prove2.me/theorems/280192e0-ff96-49de-add7-07c0892e25af
-- title:
--   The constant $K_a=\sum_{j\ge1}2^{-j}(j+3)^a$
-- statement:
--   For a real number $a\ge0$, the constant of Theorem 3.1 is the series
--
--   $$K_a=\sum_{j\ge1}2^{-j}(j+3)^a .$$
--
--   It collects the cost of the approximants of Theorem 3.1 over all accuracy scales $2^{-j}$; the theorem bounds the entropy by $6+4CK_aL$.
--
--   **Formalization Note** The summand $2^{-j}(j+3)^a$ is `KaTerm a j`, with a real exponent. $K_a$ is the `tsum` of `KaTerm a (j+1)` over $j\in\mathbb N$, i.e. over $j\ge1$. A `tsum` is $0$ for a divergent series; the series converges for every $a\ge0$, which is the first clause of the mission's statement of the bound $K_a=O(2^a a!)$.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Theorem 3.1, p.14 (PDF p.14)

import Mathlib

namespace FourierEntropyApprox

/-!
# The constant `K_a` of Theorem 3.1

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), Theorem 3.1, p.14: "where K_a = ∑_{j≥1} 2^{−j}(j + 3)^a = O(2^a a!)."

**Formalization Note.**
* `KaTerm a j = 2^{−j}(j + 3)^a` with a real exponent `a` (`Real.rpow`).
* `Ka a` is the `tsum` of `KaTerm a (j + 1)` over `j : ℕ`, i.e. over `j ≥ 1` after the shift `j ↦ j + 1`.
  A `tsum` is `0` when the series does not converge; the summability for `a ≥ 0` is the first clause of the
  mission's statement of the `K_a` bound, so the `tsum` is the page's sum.
-/

/-- The summand `2^{−j}(j + 3)^a` of `K_a` (p.14). -/
noncomputable def KaTerm (a : ℝ) (j : ℕ) : ℝ := ((2 : ℝ) ^ j)⁻¹ * ((j : ℝ) + 3) ^ a

/-- `K_a = ∑_{j ≥ 1} 2^{−j}(j + 3)^a` (p.14), as a `tsum` over `j ≥ 1`. -/
noncomputable def Ka (a : ℝ) : ℝ := ∑' j : ℕ, KaTerm a (j + 1)

end FourierEntropyApprox


