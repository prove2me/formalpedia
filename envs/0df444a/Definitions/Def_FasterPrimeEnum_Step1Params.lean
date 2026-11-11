-- Prove2me | Definitions.Def_FasterPrimeEnum_Step1Params
-- name    : FasterPrimeEnum_Step1Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:37:58.128715+00:00
-- url     : https://prove2.me/theorems/5d02f5a5-19a2-4c48-8fb1-d45f89b87395
-- title:
--   The parameters $A,\beta,T,R,Y$ of Step 1, with slack $c$
-- statement:
--   Let $N$ be large and $c\ge0$. With $L=\log N$ and $S=(\log N)^{1/2}\log\log N$, put $\tilde A=\tfrac13\log S$. A choice of integers $A,\beta,T,R,Y$ **meets Step 1 with slack $c$** if
--
--   1. $A\ge1$ and $\tilde A-c\le A<\tilde A$;
--   2. $\beta\ge0$ with $\tfrac13<2^\beta T'/S<1$, where $T'=\prod_{p\le A}p^2$ over primes $p$, and $T=2^\beta T'$;
--   3. $R\ge1$ with $|R-13\log_2\log N|\le c$;
--   4. $Y\ge2$ with $|Y-\exp(40(\log N)^{1/2}\log\log N)|\le c$.
--
--   These are the paper's choices $A=\tilde A+O(1)$, $R=13\log_2\log N+O(1)$ and $Y=\exp(40(\log N)^{1/2}\log\log N)+O(1)$, with every $O(1)$ at most $c$.
--
--   **Formalization Note** $\log$ is natural and $\log_2$ is base two, so $2^{-13\log_2\log N}=(\log N)^{-13}$. The logarithms are not clipped: the parameters are used for large $N$ only.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §10.2, Step 1, p.101

import Mathlib

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **The parameters of Step 1 of the deterministic algorithm, with slack `c`** — D. Harvey,
*Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), §10.2, Step 1,
p.101: "Let Ã := (1/3) log((log N)^{1/2} log log N) … Choose a positive integer A = Ã + O(1) with
A < Ã and define T′ := ∏_{p⩽A} p². … Choose also an integer β ⩾ 0 such that
1/3 < 2^β · T′/((log N)^{1/2} log log N) < 1 and set T := 2^β T′ = 2^β ∏_{p⩽A} p². … Finally,
choose integers R ⩾ 1 and Y ⩾ 2 such that R = 13 log₂ log N + O(1),
Y = exp(40(log N)^{1/2} log log N) + O(1)."

`Step1Params c N A β T R Y` says that `A, β, T, R, Y` are such a choice for `N`, each `O(1)` term
being at most `c` in absolute value. The product runs over the primes `p ⩽ A`.

**Formalization Note.** `log` is natural and `log₂` is base two (p.1), so `13 log₂ log N` is
`13 · logb 2 (log N)` (p.102 uses `2^{−13 log₂ log N} = (log N)^{−13}`). The parameters are used
for large `N` only, so the logarithms are not clipped here. -/
def Step1Params (c : ℝ) (N A β T R Y : ℕ) : Prop :=
  let L : ℝ := Real.log N
  let S : ℝ := Real.sqrt L * Real.log L
  let Atil : ℝ := (1 / 3) * Real.log S
  let T' : ℕ := ∏ p ∈ (Finset.range (A + 1)).filter Nat.Prime, p ^ 2
  0 < A ∧ Atil - c ≤ A ∧ (A : ℝ) < Atil ∧
    1 / 3 < (2 : ℝ) ^ β * T' / S ∧ (2 : ℝ) ^ β * T' / S < 1 ∧
    T = 2 ^ β * T' ∧
    1 ≤ R ∧ |(R : ℝ) - 13 * Real.logb 2 L| ≤ c ∧
    2 ≤ Y ∧ |(Y : ℝ) - Real.exp (40 * S)| ≤ c

end FasterPrimeEnum


