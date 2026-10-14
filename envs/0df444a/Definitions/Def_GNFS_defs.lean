-- Prove2me | Definitions.Def_GNFS_defs
-- name    : GNFS_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-13T02:22:21.187059+00:00
-- url     : https://prove2.me/theorems/54150f43-2704-4e59-8869-cbe639cbc660
-- title:
--   GNFS: base-$m$ polynomial and homogenization
-- statement:
--   Two auxiliary objects used throughout the mission.
--
--   1. **Base-$m$ polynomial.** For natural numbers $n$ and $m$, let $n = a_d m^d + \dots + a_1 m + a_0$ be the base-$m$ expansion of $n$, with digits $a_0, \dots, a_d$ (least significant first, as returned by the standard digit expansion; empty when $n = 0$). The base-$m$ polynomial of $n$ is
--   $$f_{n,m}(x) = \sum_{i=0}^{d} a_i x^i \in \mathbb{Z}[x].$$
--   2. **Homogenization.** For $f = \sum_{i=0}^{d} c_i x^i \in \mathbb{Z}[x]$ of degree $d$ and integers $a, b$,
--   $$F(a,b) = \sum_{i=0}^{d} c_i\, a^i b^{d-i} = b^d f(a/b).$$
--
--   The first is the simple polynomial-selection method of GNFS; the second is the integer $r$ attached to a relation $(a,b)$, whose smoothness the sieve tests.
--
--   **Formalization Note** Digits come from `Nat.digits m n`. For $m \le 1$ that function does not give a base-$m$ expansion, so statements about it assume $m \ge 2$. In `homogenize`, $0^0 = 1$, so $F(a,0) = c_d a^d$.
-- source:
--   Wikipedia, "General number field sieve" (revision oldid=1377718368, https://en.wikipedia.org/w/index.php?title=General_number_field_sieve&oldid=1377718368), sections 'Polynomial choice' and 'Generation of relation pairs (sieving)'

import Mathlib

/-!
# General number field sieve — definitions

Shared definitions for the Prove2Me mission proposal drafted from the Wikipedia article
"General number field sieve" (`General_number_field_sieve.pdf`).
-/

open Polynomial

namespace GNFS

/-- The base-`m` polynomial of `n`: if `n = a_d m^d + ⋯ + a_1 m + a_0` is the base-`m`
expansion of `n` (digits `0 ≤ a_i < m`), this is `f(x) = a_d x^d + ⋯ + a_1 x + a_0`. -/
noncomputable def baseMPolynomial (n m : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range (Nat.digits m n).length, C (((Nat.digits m n).getD i 0 : ℕ) : ℤ) * X ^ i

/-- The homogenization `F(a, b) = b^d f(a/b) = ∑ c_i a^i b^(d-i)` of an integer polynomial
`f = ∑ c_i x^i` of degree `d`, evaluated at a pair of integers `(a, b)`. -/
def homogenize (f : ℤ[X]) (a b : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * a ^ i * b ^ (f.natDegree - i)

end GNFS


