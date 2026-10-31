-- Prove2me | Definitions.Def_RainsSep_Distill_HasNonnegCoeffs
-- name    : RainsSep_Distill_HasNonnegCoeffs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:30.687037+00:00
-- url     : https://prove2.me/theorems/981cd425-691f-44dc-bbc3-c9034206e1a8
-- title:
--   A real polynomial has nonnegative coefficients
-- statement:
--   A polynomial $p$ in several variables with real coefficients **has nonnegative coefficients** if every coefficient of every monomial of $p$ is $\ge 0$. This is strictly stronger than $p\ge 0$ on the nonnegative orthant, and it is the form in which weight-enumerator positivity is stated.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, p. 3, before Eq. (31)

import Mathlib

namespace RainsSep.Distill

/-- **A polynomial has nonnegative coefficients.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, p. 3, before Eq. (31): "the polynomials B′(u − v, Kv, x − y, 2y) and B′(v − u, u + v,
y − x, x + y) have nonnegative coefficients".

Every coefficient of the real multivariate polynomial `p` is `≥ 0`. -/
def HasNonnegCoeffs {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ m, 0 ≤ p.coeff m

end RainsSep.Distill


