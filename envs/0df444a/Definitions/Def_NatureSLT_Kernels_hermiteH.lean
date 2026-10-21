-- Prove2me | Definitions.Def_NatureSLT_Kernels_hermiteH
-- name    : NatureSLT_Kernels_hermiteH
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:06.305067+00:00
-- url     : https://prove2.me/theorems/5d66e2c7-6dd4-4607-8ff7-314e0587d3d7
-- title:
--   Hermite polynomials $P_k(x) = (-1)^k e^{x^2} (d/dx)^k e^{-x^2}$ and the functions $H_k(x) = \mu_k P_k(x) e^{-x^2}$ of (6.23)
-- statement:
--   For an integer $k \ge 0$ and a real number $x$, the **Hermite polynomial** of the example in §6.3.1 is
--
--   $$P_k(x) = (-1)^k e^{x^2} \left(\frac{d}{dx}\right)^{k} e^{-x^2},$$
--
--   the polynomial of degree $k$ orthogonal with respect to the weight $e^{-x^2}$ on the real line ($P_0 = 1$, $P_1(x) = 2x$, $P_2(x) = 4x^2 - 2$, …). Given a sequence of **normalization constants** $\mu = (\mu_k)_{k \ge 0}$, the functions of (6.23) are
--
--   $$H_k(x) = \mu_k\, P_k(x)\, e^{-x^2}.$$
--
--   These are the one-dimensional basis functions from which the book builds the regularized Hermite kernel $\sum_i q^i H_i(x) H_i(y)$ of (6.24).
--
--   **Formalization Note** The $k$-th derivative is Mathlib's `iteratedDeriv k` of the smooth function $t \mapsto e^{-t^2}$, evaluated at $x$. $P_k$ is the physicists' family (weight $e^{-x^2}$), not Mathlib's `Polynomial.hermite` (the probabilists' family, weight $e^{-x^2/2}$). The constants $\mu_k$ are a parameter: the book calls them normalization constants without giving them.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 192, Eq. (6.23)

import Mathlib

namespace NatureSLT.Kernels

/-- The polynomial `P_k` of the Hermite example (Vapnik, *The Nature of Statistical Learning
Theory*, 2nd ed., §6.3.1, p. 192, below (6.23)):
`P_k(x) = (-1)^k e^{x²} (d/dx)^k e^{-x²}`.
This is the physicists' Hermite polynomial (weight `e^{-x²}`), not Mathlib's probabilists'
`Polynomial.hermite` (weight `e^{-x²/2}`). The `k`-th derivative is Mathlib's `iteratedDeriv` of
the smooth function `t ↦ e^{-t²}`, so it is the genuine derivative. -/
noncomputable def hermiteP (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * Real.exp (x ^ 2) * iteratedDeriv k (fun t : ℝ => Real.exp (-t ^ 2)) x

/-- The functions of (6.23) (p. 192): `H_k(x) = μ_k P_k(x) e^{-x²}`, where `μ = (μ_k)_{k ≥ 0}` are
the normalization constants, passed as a parameter. -/
noncomputable def hermiteH (μ : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  μ k * hermiteP k x * Real.exp (-x ^ 2)

end NatureSLT.Kernels


