-- Prove2me | Definitions.Def_ShorAlgorithms_DiscreteLog_IsGood
-- name    : ShorAlgorithms_DiscreteLog_IsGood
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T00:57:43.245597+00:00
-- url     : https://prove2.me/theorems/c6a3352d-2aa6-4307-a7d1-6aaccbc7e079
-- title:
--   Good outputs: conditions (6.10) and (6.11)
-- statement:
--   Let $p$ be a prime, $q$ a positive integer, $0\le r<p-1$, and $0\le c,d<q$. Write $\{z\}_q$ for the symmetric residue of $z$ modulo $q$, and set
--
--   $$
--   T=rc+d-\frac{r}{p-1}\{c(p-1)\}_q\in\mathbb R .
--   $$
--
--   The pair $(c,d)$ — equivalently every observed state $|c,d,y\rangle$ — is **good** if
--
--   1. $|\{T\}_q|=|T-jq|\le\frac12$, where $j$ is the closest integer to $T/q$ (condition (6.10)); and
--   2. $|\{c(p-1)\}_q|\le q/12$ (condition (6.11)).
--
--   Good outputs are those from which the discrete logarithm $r$ can later be recovered, and the algorithm's analysis shows that they occur with constant probability.
--
--   **Formalization Note** The real number $T$ is the auxiliary definition `phaseT`, with $p-1$ computed in $\mathbb Z$ and $\mathbb R$ (no natural-number subtraction). Condition (6.10) is stated as "there is an integer $j$ with $|T-jq|\le1/2$". This is equivalent to the page's form with $j$ the closest integer to $T/q$: since $q\ge4$, an integer $j$ with $|T-jq|\le1/2$ satisfies $|T/q-j|\le1/(2q)<1/2$, so it is the unique integer closest to $T/q$; conversely the closest integer satisfies the bound whenever any integer does.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1503, §6, eqs. (6.8), (6.10), (6.11)

import Mathlib
import Definitions.Def_ShorAlgorithms_DiscreteLog_symmRes

namespace ShorAlgorithms.DiscreteLog

/-- Shor (1997), §6, eq. (6.8), p. 1503: the real number
`T = r c + d - (r/(p-1)) {c(p-1)}_q`. Here `p - 1` is computed in `ℤ` and `ℝ` (as
`(p : ℤ) - 1`, `(p : ℝ) - 1`), not by natural-number subtraction. -/
noncomputable def phaseT (p q r : ℕ) (c d : Fin q) : ℝ :=
  (r : ℝ) * ((c : ℕ) : ℝ) + ((d : ℕ) : ℝ)
    - (r : ℝ) / ((p : ℝ) - 1) * (symmRes (q : ℤ) (((c : ℕ) : ℤ) * ((p : ℤ) - 1)) : ℝ)

/-- Shor (1997), §6, eqs. (6.10)–(6.11), p. 1503: an output `|c, d, y⟩` is *good* when
`|{T}_q| ≤ 1/2`, i.e. `|T - j q| ≤ 1/2` for an integer `j` (the page's `j`, the closest integer
to `T/q`), and `|{c(p-1)}_q| ≤ q/12`. Goodness depends only on `(c, d)`. -/
def IsGood (p q r : ℕ) (c d : Fin q) : Prop :=
  (∃ j : ℤ, |phaseT p q r c d - (j : ℝ) * (q : ℝ)| ≤ 1 / 2) ∧
    |(symmRes (q : ℤ) (((c : ℕ) : ℤ) * ((p : ℤ) - 1)) : ℝ)| ≤ (q : ℝ) / 12

end ShorAlgorithms.DiscreteLog


