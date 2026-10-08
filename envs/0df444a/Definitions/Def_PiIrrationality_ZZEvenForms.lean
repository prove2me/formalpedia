-- Prove2me | Definitions.Def_PiIrrationality_ZZEvenForms
-- name    : PiIrrationality_ZZEvenForms
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-05T09:28:39.386566+00:00
-- url     : https://prove2.me/theorems/01b4e42c-171e-4b26-a820-2c8ab35b41fe
-- title:
--   Even-index Zeilberger–Zudilin integrals, positive coefficient and normaliser
-- statement:
--   This file fixes the objects of the even-index Zeilberger–Zudilin construction for $\pi$, in the normalisation of Bai with exponents $(a,b,c)=(2,4,6)$.
--
--   For $n\ge 0$ let
--   $$
--   R_n(t)=\frac{5\,t^{4n}\,(t^4+6t^2+25)^{4n}}{(25-t^2)^{6n+1}},
--   \qquad
--   J_n=i\int_{-1-2i}^{-1+2i}R_n(t)\,dt=-\int_{-2}^{2}R_n(-1+is)\,ds ,
--   $$
--   the integral being taken along the vertical segment $\operatorname{Re}t=-1$, where $R_n$ has no poles. Up to sign, $J_n$ is the Zeilberger–Zudilin integral $I_{2n}$.
--
--   Let $A(z)=(1+z)^4\,(2+6z+9z^2+6z^3+2z^4)^4$ and
--   $$
--   \mathrm{coef}_n=[z^{6n}]\,\frac{A(z)^n}{(1-z)^{8n}}=\sum_{k=0}^{6n}[z^k]A(z)^n\binom{8n-1+6n-k}{6n-k},
--   $$
--   a positive integer. It is the coefficient of $z^{6n}$ in $S(z)^n$, where $S(z)=A(z)/(1-z)^8$.
--
--   Bai's set of deleted primes $P_n$ consists of the primes $p$ with $\max(5,\sqrt{8n})<p\le 8n$ and
--   $$
--   \left\{\frac{2n}{p}+\frac12\right\}+2\left\{\frac{4n}{p}\right\}<\left\{\frac{6n}{p}\right\},
--   $$
--   where $\{x\}=x-\lfloor x\rfloor$. Put $\Phi_n=\prod_{p\in P_n}p$ and define the normalising multiplier
--   $$
--   M_n=\frac{2^{4}\operatorname{lcm}(1,2,\dots,8n)}{2^{5n}\,\Phi_n}.
--   $$
--
--   With these objects, $M_nJ_n$ is an integer linear form in $1$ and $\pi$ whose $\pi$-coefficient is $-M_n16^n\mathrm{coef}_n/4$. The decay of $J_n$ and the growth of $\mathrm{coef}_n$, $\operatorname{lcm}(1,\dots,8n)$ and $\Phi_n$ then give upper bounds for the irrationality measure of $\pi$.
--
--   **Formalization Note.** `J n` is written along the parametrisation $t=-1+is$. The condition $\sqrt{8n}<p$ is encoded as $8n<p^2$, and fractional parts are taken in $\mathbb{Q}$. `Nat.lcmUpto m` is Mathlib's $\operatorname{lcm}(1,\dots,m)$.
-- source:
--   D. Zeilberger and W. Zudilin, The irrationality measure of π is at most 7.103205334137…, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, arXiv:1912.06345, equation (1) and Part II; Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), equations (1.8), (2.14), (2.35), (4.4)–(4.5), with (a,b,c)=(2,4,6).

import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor

/-!
# Even-index Zeilberger–Zudilin linear forms for π

Objects for the linear forms of D. Zeilberger and W. Zudilin, "The irrationality
measure of π is at most 7.103205334137…" (arXiv:1912.06345), at even index, in
the normalisation of Y. Bai (arXiv:2609.11276, Sections 1–4) with exponents
(a, b, c) = (2, 4, 6).
-/

namespace PiIrrationality.ZZEven

open Complex Polynomial

/-- The integrand `R_n(t) = 5 t^{4n} (t^4+6t^2+25)^{4n} / (25-t^2)^{6n+1}`. -/
noncomputable def R (n : ℕ) (t : ℂ) : ℂ :=
  5 * t ^ (4 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (4 * n) / (25 - t ^ 2) ^ (6 * n + 1)

/-- `J_n = i ∫_{-1-2i}^{-1+2i} R_n(t) dt`, written along the parametrisation
`t = -1 + i s`, `-2 ≤ s ≤ 2`. -/
noncomputable def J (n : ℕ) : ℂ :=
  -∫ s in (-2 : ℝ)..2, R n (-1 + (s : ℂ) * I)

/-- The polynomial `A(z) = (1+z)^4 (2+6z+9z^2+6z^3+2z^4)^4` with natural coefficients. -/
noncomputable def A : ℕ[X] :=
  (1 + X) ^ 4 * (C 2 + C 6 * X + C 9 * X ^ 2 + C 6 * X ^ 3 + C 2 * X ^ 4) ^ 4

/-- `coef n = [z^{6n}] A(z)^n (1-z)^{-8n}`, the coefficient of `z^{6n}` in `S(z)^n` with
`S(z) = (1+z)^4 (2+6z+9z^2+6z^3+2z^4)^4 / (1-z)^8`. -/
noncomputable def coef (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (6 * n + 1),
    (A ^ n).coeff k * Nat.choose (8 * n - 1 + (6 * n - k)) (6 * n - k)

/-- Bai's set of deleted primes for the exponents `(2,4,6)`: primes `p` with
`max(5, √(8n)) < p ≤ 8n` and `{2n/p + 1/2} + 2{4n/p} < {6n/p}`. -/
def deletedPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (8 * n + 1)).filter fun p =>
    p.Prime ∧ 5 < p ∧ 8 * n < p ^ 2 ∧
      Int.fract ((2 * n : ℚ) / p + 1 / 2) + 2 * Int.fract ((4 * n : ℚ) / p) <
        Int.fract ((6 * n : ℚ) / p)

/-- The product `Φ_n` of the deleted primes. -/
def Phi (n : ℕ) : ℕ := ∏ p ∈ deletedPrimes n, p

/-- The normalising multiplier `M_n = 2^{4-5n} lcm(1,…,8n) / Φ_n`. -/
noncomputable def M (n : ℕ) : ℝ :=
  2 ^ 4 * (Nat.lcmUpto (8 * n) : ℝ) / (2 ^ (5 * n) * (Phi n : ℝ))

end PiIrrationality.ZZEven


