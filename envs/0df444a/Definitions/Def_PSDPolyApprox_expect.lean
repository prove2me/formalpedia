-- Prove2me | Definitions.Def_PSDPolyApprox_expect
-- name    : PSDPolyApprox_expect
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:51.114533+00:00
-- url     : https://prove2.me/theorems/96be1e37-36ba-49b9-a233-9aae9a344fda
-- title:
--   Expectation $\mathbb E[f]$ under the uniform measure on $H_n$
-- statement:
--   For $f:H_n\to\mathbb R$, the expectation of $f$ under the uniform probability measure $\mu$ on the hypercube is
--   $$
--   \mathbb E[f]=\mathbb E_{x\sim\mu}f(x)=\frac1{2^n}\sum_{x\in H_n}f(x).
--   $$
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §2.1, p.3

import Mathlib
import Definitions.Def_PSDPolyApprox_Cube

namespace PSDPolyApprox

/-- **Expectation under the uniform measure on the hypercube**, `E[f] = E_{x∼µ} f(x)`.
Fawzi, arXiv:1811.09649v1, §2.1, p.3: "let µ be the uniform probability measure on Hn".

`expect f = 2⁻ⁿ ∑_{x ∈ Hₙ} f(x)`. -/
noncomputable def expect {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : Cube n, f x

end PSDPolyApprox


