-- Prove2me | Definitions.Def_Gelbart_theta_coeff
-- name    : Gelbart_theta_coeff
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T03:34:47.020058+00:00
-- url     : https://prove2.me/theorems/29f94aa7-59d3-4ddd-9d23-dd91b71d37e0
-- title:
--   Fourier coefficients of Jacobi's $\theta$
-- statement:
--   The coefficient sequence for which the general construction reproduces Jacobi's theta function: $$\theta(z) = \sum_{m \in \mathbb{Z}} e^{\pi i m^{2} z} = \sum_{n \ge 0} c_n e^{2\pi i n z/2}, \qquad c_0 = 1,\ c_n = 2 \ (n \ge 1 \text{ a perfect square}),\ c_n = 0 \text{ otherwise},$$ i.e. $c_n$ counts the integers $m$ with $m^2 = n$. This is the sequence used in Riemann's derivation of the functional equation of $\zeta$ recalled by Gelbart on p. 187.
-- source:
--   S. Gelbart, An elementary introduction to the Langlands program, Bull. Amer. Math. Soc. (N.S.) 10 (1984), no. 2, 177-219, https://doi.org/10.1090/S0273-0979-1984-15237-6, p. 187, §II.B.2

import Mathlib

namespace Gelbart

/-- The coefficient sequence of Jacobi's theta function
`θ (z) = ∑_{m ∈ ℤ} exp (πim²z) = ∑_{n ≥ 0} thetaCoeff n * exp (2πinz/2)`:
`thetaCoeff n = 1` for `n = 0`, `= 2` if `n ≥ 1` is a perfect square, `= 0` otherwise. -/
def thetaCoeff (n : ℕ) : ℂ :=
  if Nat.sqrt n * Nat.sqrt n = n then (if n = 0 then 1 else 2) else 0

end Gelbart


