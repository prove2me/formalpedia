-- Prove2me | Definitions.Def_SpikedWishart_Separated_GUE
-- name    : SpikedWishart_Separated_GUE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:05.382899+00:00
-- url     : https://prove2.me/theorems/ff48c5f0-e42c-49a2-925c-1fc607aa057d
-- title:
--   §1.2.2, pp. 1648–1649, (27)–(34) — Z_k, the finite-GUE law G_k, Hermite polynomials p_n, kernel H^(k), Fredholm determinant
-- statement:
--   This file defines the limit law of the mission and its Fredholm-determinant representation.
--
--   1. For $k \ge 1$ the **GUE eigenvalue weight** on $\mathbb R^k$ is $w_k(\xi) = \prod_{1\le i<j\le k}|\xi_i-\xi_j|^2 \prod_{i=1}^k e^{-\xi_i^2/2}$, and $Z_k = \int_{\mathbb R^k} w_k(\xi)\,d\xi$ is its total mass (27).
--   2. **Definition 1.2** (28): the distribution of the largest eigenvalue of the $k\times k$ GUE is
--   $$
--   G_k(x) = \frac1{Z_k}\int_{-\infty}^x\!\!\cdots\int_{-\infty}^x w_k(\xi)\,d\xi_1\cdots d\xi_k .
--   $$
--   3. The **orthonormal polynomials** for the weight $e^{-x^2/2}$ (30)–(31) are $p_n(\xi) = \mathrm{He}_n(\xi)/\big((2\pi)^{1/4}\sqrt{n!}\big)$, where $\mathrm{He}_n$ is the probabilists' Hermite polynomial ($\mathrm{He}_0 = 1$, $\mathrm{He}_{n+1} = x\mathrm{He}_n - \mathrm{He}_n'$). Their leading coefficients are $c_n = 1/\big((2\pi)^{1/4}\sqrt{n!}\big)$ (32).
--   4. The **kernel** (34) is
--   $$
--   H^{(k)}(u,v) = \frac{c_{k-1}}{c_k}\,\frac{p_k(u)p_{k-1}(v) - p_{k-1}(u)p_k(v)}{u-v}\,e^{-(u^2+v^2)/4}, \qquad u \ne v,
--   $$
--   and on the diagonal it takes its continuous value $\frac{c_{k-1}}{c_k}\big(p_k'(u)p_{k-1}(u) - p_{k-1}'(u)p_k(u)\big)e^{-u^2/2}$.
--   5. The **Fredholm determinant** $\det(1-K)$ of an integral operator with kernel $K$ on $L^2((x,\infty))$ is the Fredholm series
--   $$
--   \det(1-K_x) = \sum_{n\ge0}\frac{(-1)^n}{n!}\int_{(x,\infty)^n}\det\big[K(u_i,u_j)\big]_{i,j=1}^n\,du_1\cdots du_n .
--   $$
--
--   $G_k$ is the limit law in Theorem 1.1(b), and the kernel $H^{(k)}$ gives its Fredholm-determinant form (Lemma 1.1).
--
--   **Formalization Note** The paper writes $p_n$ through the physicists' $H_n$ as $p_n(\xi) = H_n(\xi/\sqrt2)/\big((2\pi)^{1/4}2^{n/2}\sqrt{n!}\big)$; since $H_n(\xi/\sqrt2) = 2^{n/2}\mathrm{He}_n(\xi)$ this is the same polynomial. $Z_k$ is the integral itself, not its closed form $(2\pi)^{k/2}\prod_{j=1}^k j!$. The diagonal branch of $H^{(k)}$ is needed because Lean's division by $0$ returns $0$ and the Fredholm series evaluates the kernel on the diagonal. The Fredholm series equals the operator determinant $\det(1-K)$ for trace-class operators with continuous kernels (Fredholm's theorem).
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1648–1649, §1.2.2, (26)–(28), Definition 1.2, (30)–(32), (34)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy

open MeasureTheory Set

namespace SpikedWishart.Separated

/-- The GUE eigenvalue weight `Π_{i<j} |ξ_i − ξ_j|² · Π_i e^{−ξ_i²/2}` of (26)–(28). -/
noncomputable def gueWeight (k : ℕ) (ξ : Fin k → ℝ) : ℝ :=
  (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, |ξ i - ξ j| ^ 2) * ∏ i : Fin k, Real.exp (-(1 / 2) * ξ i ^ 2)

/-- (27): the normalising constant `Z_k`, as the integral of the weight over `ℝ^k`
(not its closed form). -/
noncomputable def Z (k : ℕ) : ℝ :=
  ∫ ξ : Fin k → ℝ, gueWeight k ξ

/-- Definition 1.2, (28): `G_k(x)`, the distribution function of the largest eigenvalue of
the `k × k` GUE. -/
noncomputable def G (k : ℕ) (x : ℝ) : ℝ :=
  (1 / Z k) * ∫ ξ in Set.pi univ (fun _ : Fin k => Iic x), gueWeight k ξ

/-- (31): the orthonormal polynomial `p_n` for the weight `e^{−x²/2}`, written with Mathlib's
probabilists' Hermite polynomial `He_n = Polynomial.hermite n`:
`p_n(ξ) = He_n(ξ) / ((2π)^{1/4} √n!)`, which equals (31) since `H_n(ξ/√2) = 2^{n/2} He_n(ξ)`. -/
noncomputable def p (n : ℕ) (ξ : ℝ) : ℝ :=
  Polynomial.aeval ξ (Polynomial.hermite n) / ((2 * Real.pi) ^ (1 / 4 : ℝ) * Real.sqrt n.factorial)

/-- (32): the leading coefficient `c_n = 1 / ((2π)^{1/4} √n!)` of `p_n`. -/
noncomputable def c (n : ℕ) : ℝ :=
  1 / ((2 * Real.pi) ^ (1 / 4 : ℝ) * Real.sqrt n.factorial)

/-- (34): the kernel `H^{(k)}(u, v)`, with its continuous value on the diagonal
`u = v` (the limit of the divided difference). -/
noncomputable def Hk (k : ℕ) (u v : ℝ) : ℝ :=
  if u = v then
    (c (k - 1) / c k) * (deriv (p k) u * p (k - 1) u - deriv (p (k - 1)) u * p k u) *
      Real.exp (-(u ^ 2) / 2)
  else
    (c (k - 1) / c k) * ((p k u * p (k - 1) v - p (k - 1) u * p k v) / (u - v)) *
      Real.exp (-(u ^ 2 + v ^ 2) / 4)

end SpikedWishart.Separated


