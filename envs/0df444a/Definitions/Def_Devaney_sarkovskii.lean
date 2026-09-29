-- Prove2me | Definitions.Def_Devaney_sarkovskii
-- name    : Devaney_sarkovskii
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T06:57:52.01441+00:00
-- url     : https://prove2.me/theorems/41e1b781-5152-4b1a-b863-aeca63bedd8d
-- title:
--   Prime period, the Sarkovskii ordering, and interval covering
-- statement:
--   The vocabulary of Sarkovskii's theorem.
--
--   **Prime period.** A point $x$ has prime period $n \ge 1$ for $f$ if $f^{n}(x) = x$ and $f^{m}(x) \ne x$ for every $0 < m < n$.
--
--   **The Sarkovskii ordering.** Every positive integer is uniquely $2^{a}p$ with $p$ odd; write $a = v_2(n)$ for the $2$-adic valuation and $p = \mathrm{odd}(n)$ for the odd part. The ordering
--
--   $$3 \triangleright 5 \triangleright 7 \triangleright \cdots \triangleright 2\cdot3 \triangleright 2\cdot5 \triangleright \cdots \triangleright 2^2\cdot3 \triangleright \cdots \triangleright 2^3 \triangleright 2^2 \triangleright 2 \triangleright 1$$
--
--   lists the odd numbers greater than one first, then their doubles, then their multiples by $4$, and so on, with the powers of two last in decreasing order. Formally $k \triangleright \ell$ when: both odd parts exceed $1$ and $(v_2(k), \mathrm{odd}(k))$ is lexicographically smaller than $(v_2(\ell), \mathrm{odd}(\ell))$; or $\mathrm{odd}(k) > 1$ and $\ell$ is a positive power of two; or both are powers of two and $v_2(\ell) < v_2(k)$.
--
--   **Covering.** For sets $I, J$, one says $f(I)$ *covers* $J$ when $J \subseteq f(I)$. Chains of covering intervals are the engine of the proof.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.10, pp. 60–62 (prime period; the Sarkovskii ordering; the covering relation)

import Mathlib

namespace Devaney

/-- `x` is a periodic point of prime period `n` for `f`: the `n`-th iterate returns `x` to
itself and no smaller positive iterate does. -/
def HasPrimePeriod (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : Prop :=
  0 < n ∧ f^[n] x = x ∧ ∀ m, 0 < m → m < n → f^[m] x ≠ x

/-- The exponent of `2` in `n`. -/
def twoAdicVal (n : ℕ) : ℕ := padicValNat 2 n

/-- The odd part of `n`, i.e. `n / 2 ^ twoAdicVal n`. -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ padicValNat 2 n

/-- Devaney, §1.10: the Sarkovskii ordering of the positive integers,
$$3 \triangleright 5 \triangleright 7 \triangleright \cdots \triangleright 2\cdot 3 \triangleright
2 \cdot 5 \triangleright \cdots \triangleright 2^2 \cdot 3 \triangleright \cdots \triangleright
2^3 \triangleright 2^2 \triangleright 2 \triangleright 1 .$$
`SarkovskiiPrecedes k l` says that `k` comes strictly before `l`: writing `k = 2^a * p` and
`l = 2^b * q` with `p`, `q` odd, either both `p, q > 1` and `(a, p)` is lexicographically
smaller than `(b, q)`; or `p > 1` and `q = 1`; or both are powers of two and `b < a`. -/
def SarkovskiiPrecedes (k l : ℕ) : Prop :=
  (1 < oddPart k ∧ 1 < oddPart l ∧
      (twoAdicVal k < twoAdicVal l ∨
        (twoAdicVal k = twoAdicVal l ∧ oddPart k < oddPart l))) ∨
  (1 < oddPart k ∧ oddPart l = 1 ∧ 0 < l) ∨
  (oddPart k = 1 ∧ oddPart l = 1 ∧ 0 < l ∧ twoAdicVal l < twoAdicVal k)

/-- Devaney, §1.10: `f(I)` *covers* `J` when the image of `I` under `f` contains `J`. -/
def Covers (f : ℝ → ℝ) (I J : Set ℝ) : Prop := J ⊆ f '' I

end Devaney


