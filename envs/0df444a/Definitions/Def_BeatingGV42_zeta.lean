-- Prove2me | Definitions.Def_BeatingGV42_zeta
-- name    : BeatingGV42_zeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:58.455655+00:00
-- url     : https://prove2.me/theorems/f16486a0-f95a-4e96-9ecc-703a1f5b704a
-- title:
--   The zeta function $Z_F(T)$ and coefficient extraction $[T^r]$
-- statement:
--   For a function field $F/\mathbb F_Q$ the **zeta function** is the power series
--   $$
--   Z_F(T)=\sum_{r=0}^{\infty}\bigl|\{E\in\operatorname{Div}(F):E\ge 0,\ \deg E=r\}\bigr|\,T^r ,
--   $$
--   whose coefficients count effective divisors by degree. For a power series $A(T)$ and an integer $r$, $[T^r]A(T)$ is the coefficient of $T^r$, **interpreted as zero when $r<0$**. For real $t$, $Z_F(t)=\sum_{r\ge 0}|\{E\ge 0,\deg E=r\}|\,t^r$ is the value of the series at $t$; it converges for $0\le t<1/Q$.
--
--   The zeta function counts the divisors $H$ that index codewords of the mother codes (Lemma 4.3), and its values at $0<t<1/Q$ bound those counts (Corollary 4.5).
--
--   **Formalization Note** `effCount k F r` is the number of effective divisors of degree $r$ (a `Nat.card`, the same sequence as in the platform's `AlgebraicCurve.exists_LPolynomial_of_finite`), `zeta k F` is `PowerSeries.mk` of it over $\mathbb Z$, `coeffZ r A` is $[T^r]A$ with value $0$ for $r<0$, and `zetaAt k F t` is a `tsum` (junk $0$ outside the range of convergence, which no statement uses). The Euler product $\prod_P(1-T^{\deg P})^{-1}$ is a theorem, not part of the definition.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §3, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace BeatingGV42

/-- The number of effective divisors of degree `r`,
`|{E ∈ Div(F) : E ≥ 0, deg E = r}|` (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, p.11 (PDF p.13)).

**Formalization Note** `Nat.card` of the subtype; it is the same coefficient sequence as in the
platform's `AlgebraicCurve.exists_LPolynomial_of_finite`, and is finite for a function field over a
finite field (so the junk value `0` of an infinite `Nat.card` does not occur). -/
noncomputable def effCount (k F : Type*) [Field k] [Field F] [Algebra k F] (r : ℕ) : ℕ :=
  Nat.card {E : Divisor k F // 0 ≤ E ∧ Divisor.degree E = (r : ℤ)}

/-- **The zeta function** of `F/F_Q` as a formal power series
`Z_F(T) = Σ_{r ≥ 0} |{E ∈ Div(F) : E ≥ 0, deg E = r}| T^r` (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, p.11 (PDF p.13)).

**Formalization Note** A power series with integer coefficients `effCount k F r`. The Euler-product
form `Π_P (1 − T^{deg P})^{−1}` is a theorem, not part of the definition. -/
noncomputable def zeta (k F : Type*) [Field k] [Field F] [Algebra k F] : PowerSeries ℤ :=
  PowerSeries.mk fun r => (effCount k F r : ℤ)

/-- **Coefficient extraction** `[T^r] A(T)` for an integer `r` (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, p.11 (PDF p.13)):
"We write [T^r]A(T) for the coefficient of T^r in a power series A(T), interpreted as zero when
r < 0." -/
noncomputable def coeffZ (r : ℤ) (A : PowerSeries ℤ) : ℤ :=
  if r < 0 then 0 else PowerSeries.coeff r.toNat A

/-- **The zeta function evaluated at a real `t`**, `Z_F(t) = Σ_{r ≥ 0} |{E ≥ 0, deg E = r}| t^r`
(Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, p.11 (PDF p.13); used at `0 < t < 1/Q` in Corollary 4.5 and Lemma 4.8).

**Formalization Note** A `tsum`. The series converges for `0 ≤ t < 1/Q` (the coefficients grow like
`h_F Q^r/(Q − 1)`); outside that range `tsum` returns the junk value `0`, and no statement uses
`zetaAt` there. -/
noncomputable def zetaAt (k F : Type*) [Field k] [Field F] [Algebra k F] (t : ℝ) : ℝ :=
  ∑' r : ℕ, (effCount k F r : ℝ) * t ^ r

end BeatingGV42


