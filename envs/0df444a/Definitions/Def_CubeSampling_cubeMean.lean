-- Prove2me | Definitions.Def_CubeSampling_cubeMean
-- name    : CubeSampling_cubeMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:58.401196+00:00
-- url     : https://prove2.me/theorems/f2d1a183-da70-40bb-ab1b-049839a3519d
-- title:
--   Expectation $\mathbb E[f]$ under the uniform measure $\mu_d$
-- statement:
--   Let $\mu_d$ be the uniform probability measure on $\{-1,1\}^d$. For $f : \{-1,1\}^d \to \mathbb R$,
--   $$
--   \mathbb E[f] = \int f\,d\mu_d = 2^{-d}\sum_{x \in \{-1,1\}^d} f(x).
--   $$
--   The norm and inner product of the mission are $\|f\|_2^2 = \mathbb E[f^2]$ and $\langle f, g\rangle = \mathbb E[fg]$.
--
--   **Formalization Note** Defined as the average over the $2^d$ points; that it equals the integral against the uniform probability measure is checked separately.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib
import Definitions.Def_CubeSampling_Cube

namespace CubeSampling

/-- The expectation `E[f] = ∫ f dμ_d` under the uniform measure `μ_d` on `{−1, 1}^d`
(Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3): the average `2^{−d} ∑_x f(x)`.

**Formalization Note** On the finite cube the integral against the uniform probability measure
is this average (sanity file `CubeSampling_sanity`); `‖f‖₂² = cubeMean d (f²)` and
`⟨f, g⟩ = cubeMean d (f g)`. -/
noncomputable def cubeMean (d : ℕ) (f : Cube d → ℝ) : ℝ := ((2 : ℝ) ^ d)⁻¹ * ∑ x : Cube d, f x

end CubeSampling


