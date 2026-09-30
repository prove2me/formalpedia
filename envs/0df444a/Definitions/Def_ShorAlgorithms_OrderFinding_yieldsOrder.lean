-- Prove2me | Definitions.Def_ShorAlgorithms_OrderFinding_yieldsOrder
-- name    : ShorAlgorithms_OrderFinding_yieldsOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T09:11:11.761619+00:00
-- url     : https://prove2.me/theorems/9f25b4d8-3bb4-42a3-9be9-a24a883c4c23
-- title:
--   Rounding $c/q$ to a fraction with denominator below $n$ returns denominator $r$
-- statement:
--   Let $n, q, r$ be natural numbers and $0 \le c < q$ the observed value of the first register. After the measurement the algorithm rounds $c/q$ to the nearest fraction whose denominator (in lowest terms) is smaller than $n$. We say that **$c$ gives us $r$** when
--
--   1. some rational $s$ with lowest-terms denominator smaller than $n$ satisfies $\left|\frac{c}{q} - s\right| \le \frac{1}{2q}$, and
--   2. every rational $s$ with lowest-terms denominator smaller than $n$ and $\left|\frac{c}{q} - s\right| \le \frac{1}{2q}$ has lowest-terms denominator exactly $r$.
--
--   In that case the nearest fraction to $c/q$ with denominator smaller than $n$ lies within $1/2q$ of $c/q$, so its denominator in lowest terms is $r$, and rounding returns the order.
--
--   **Formalization Note** `Rat.den` is the denominator of a rational number in lowest terms, which is the paper's "the fraction $d/r$ in lowest terms". The distances are computed in `ℚ` with `(c : ℚ) / q`.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1500, §5, "Thus, we can obtain the fraction d/r in lowest terms by rounding c/q to the nearest fraction having a denominator smaller than n" and "If we have the fraction d/r in lowest terms, and if d happens to be relatively prime to r, this will give us r"

import Mathlib

namespace ShorAlgorithms.OrderFinding

/-- Shor (1997), §5, p. 1500: the observed value `c` *gives us `r`* by rounding. Some fraction
with lowest-terms denominator smaller than `n` lies within `1/(2q)` of `c/q`, and every such
fraction has lowest-terms denominator exactly `r`. Rounding `c/q` to the nearest fraction with
denominator smaller than `n` then returns a fraction in lowest terms with denominator `r`.
(`Rat.den` is the denominator in lowest terms.) -/
def yieldsOrder (n q r c : ℕ) : Prop :=
  (∃ s : ℚ, s.den < n ∧ |(c : ℚ) / q - s| ≤ 1 / (2 * q)) ∧
    ∀ s : ℚ, s.den < n → |(c : ℚ) / q - s| ≤ 1 / (2 * q) → s.den = r

end ShorAlgorithms.OrderFinding


