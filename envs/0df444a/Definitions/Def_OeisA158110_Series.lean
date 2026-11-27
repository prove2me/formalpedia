-- Prove2me | Definitions.Def_OeisA158110_Series
-- name    : OeisA158110_Series
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-27T04:48:20.543802+00:00
-- url     : https://prove2.me/theorems/0037fde5-6ec2-498f-bd30-1867fb13fdee
-- title:
--   OEIS A158110: the series $\logSeries$ and its exponential coefficients $a(n)$
-- statement:
--   For natural numbers $q$ and $m$, let $L_{q,m}$ be the rational power series whose coefficient of $x^n$ is $0$ when $n = 0$ and $q^{n^m}/n$ when $n \ge 1$:
--
--   $$L_{q,m} = \sum_{n \ge 1} \frac{q^{n^m}}{n} x^n \in \mathbb{Q}[\![x]\!].$$
--
--   The sum starts at $n = 1$, so the exponent $n^m$ is at least $1$ and the indeterminate expression $0^0$ never occurs. The second definition fixes $q = 2$ and $m = 3$ and names the coefficients of the composed series $\exp(L_{2,3})$: $a(n)$ is the coefficient of $x^n$ in $\exp\!\left(\sum_{n \ge 1} 2^{n^3} x^n / n\right)$. These coefficients form OEIS sequence A158110.
--
--   **Formalization Note.** Lean represents $L_{q,m}$ as `logSeries q m`, built with `PowerSeries.mk` from its coefficient function, and $a(n)$ as `coeff n (subst (logSeries 2 3) (exp ℚ))`, where `subst` is power-series composition and `exp ℚ` is the exponential series over $\mathbb{Q}$.
-- source:
--   OEIS A158110, Paul D. Hanna, 2009, https://oeis.org/A158110 — the sequence of coefficients of exp(sum_{n>=1} 2^(n^3) x^n / n). Lean source transplanted verbatim (definitions and theorem statements) from google-deepmind/formal-conjectures, FormalConjectures/OEIS/158110.lean, commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53. Integrality conjecture in A158110 proved by Sela Fried, 'Proof of a conjecture stated in A158110', 2025, https://oeis.org/A158110/a158110.pdf

import Mathlib

namespace OeisA158110

open PowerSeries

/-- The series $\sum_{n \ge 1} q^{n^m} x^n / n$ over $\mathbb{Q}$. The sum starts at $n = 1$,
so the exponent $n^m$ is at least $1$ and $0^0$ never occurs. -/
noncomputable def logSeries (q m : ℕ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else (q : ℚ) ^ (n ^ m) / n

/-- The coefficients of $\exp\left(\sum_{n \ge 1} 2^{n^3} x^n / n\right)$, the sequence A158110.
`subst L (exp ℚ)` is the composition $\exp \circ L$. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n (subst (logSeries 2 3) (exp ℚ))

end OeisA158110


