-- Prove2me | Definitions.Def_CleveDiVincenzo_Schumacher_schumacher
-- name    : CleveDiVincenzo_Schumacher_schumacher
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:35.19385+00:00
-- url     : https://prove2.me/theorems/ac15786e-239b-4583-98a4-8e04b04a0887
-- title:
--   The Schumacher coding function $f(x)=\sum_{i<m}\binom ni+I[x,n,m]$
-- statement:
--   An $n$-bit string $x_{n-1}\cdots x_0$ is identified with the binary number $x\in\{0,\dots,2^n-1\}$; $x_{n-1}$ is the first, most significant bit. Its **weight** is the number of 1's,
--   $$
--   m=\sum_{k=0}^{n-1}x_k .
--   $$
--   The **block start** of weight $m$ is $\sum_{i=0}^{m-1}\binom ni$: the strings with exactly $m$ ones are sent to the states $\sum_{i=0}^{m-1}\binom ni,\dots,\sum_{i=0}^{m}\binom ni-1$. The **index number** $I[x,n,m]$ is the position of $x$ inside its block, the number of $n$-bit strings $z$ with the same weight as $x$ and $z<x$. The **Schumacher coding function** is
--   $$
--   f(x)=\sum_{i=0}^{m-1}\binom ni+I[x,n,m],\qquad m=\text{the weight of }x .
--   $$
--
--   This is the permutation of the $2^n$ basis states $|0\rangle,\dots,|2^n-1\rangle$ that Schumacher's quantum data compression applies: it sorts the states by their number of 1's, keeping the numerical order inside each weight class, so that the typical (low-weight) states come first. Every theorem of the mission is about this function.
--
--   **Formalization Note** The weight counts the indices $k\le\log_2 x$ with bit $k$ of $x$ set (for $x<2^n$ this is $\sum_{k<n}x_k$). The paper keeps "lexicographical ordering within each block"; for fixed-length strings written most significant bit first this is numerical order, the order Eqs. (7)–(9) and (11) use, so `index n x` counts the $z<2^n$ with `weight z = weight x` and $z<x$. The weight $m$ is not a separate argument of `index`. $f$ is defined by Eq. (6) directly, not by Eq. (12) and not through a program; its value on $x\ge 2^n$ is never used.
-- source:
--   Cleve, DiVincenzo, Schumacher's quantum data compression as a quantum computation, arXiv:quant-ph/9603009v1, §II, Eqs. (4)–(6), p.8 (f, blocks, I[x,n,m]); Eq. (22), p.15 (m = Σ x_k); bit convention p.6 and Eq. (11), p.9

import Mathlib

namespace CleveDiVincenzo.Schumacher

/-- The **weight** of a binary string: the number `m = Σ_{k=0}^{n−1} x_k` of 1's in the binary
expansion of `x` (Cleve, DiVincenzo, *Schumacher's quantum data compression as a quantum
computation*, arXiv:quant-ph/9603009v1, Eq. (22), p.15).

**Formalization Note** An `n`-bit string `x_{n−1} … x_0` is the natural number `x < 2^n`
(p.6 and Eq. (11), p.9: `x_p` is bit `p`, `x_{n−1}` the most significant). The weight counts the
indices `k ≤ log₂ x` with `Nat.testBit x k = true`; every 1-bit of `x` has such an index, so for
`x < 2^n` this is exactly `Σ_{k=0}^{n−1} x_k` (and `weight 0 = 0`). -/
def weight (x : ℕ) : ℕ :=
  ((List.range (Nat.log2 x + 1)).filter fun k => x.testBit k).length

/-- The start of the weight-`m` block, `Σ_{i=0}^{m−1} C(n,i)` (Cleve, DiVincenzo,
arXiv:quant-ph/9603009v1, Eq. (4), p.8): the `n`-bit strings with exactly `m` ones are sent to
the states `Σ_{i=0}^{m−1} C(n,i), …, Σ_{i=0}^{m} C(n,i) − 1` (Eqs. (4)–(5)).
`blockStart n 0 = 0`. -/
def blockStart (n m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, n.choose i

/-- The **index number** `I[x, n, m]` (Cleve, DiVincenzo, arXiv:quant-ph/9603009v1, §II, p.8):
the position of `x` inside its weight block, i.e. the number of `n`-bit strings `z` with the
same number `m` of 1's as `x` that come before `x`.

**Formalization Note** The paper "preserve[s] lexicographical ordering within each block" (p.8).
For strings `x_{n−1} … x_0` of a fixed length `n`, written most significant bit first,
lexicographic order is numerical order of `z`, which is the order Eqs. (7)–(9) and (11) use
(strings with more leading zeros have smaller index). So `I[x,n,m]` is the number of
`z < 2^n` with `weight z = weight x` and `z < x`. The weight `m` is not a separate argument:
it is always the weight of `x`. -/
def index (n x : ℕ) : ℕ :=
  ((Finset.range (2 ^ n)).filter fun z => weight z = weight x ∧ z < x).card

/-- The **Schumacher coding function** `f` (Cleve, DiVincenzo, arXiv:quant-ph/9603009v1, §II,
Eq. (6), p.8): for an `n`-bit string `x` with `m` ones,
`f(x) = Σ_{i=0}^{m−1} C(n,i) + I[x, n, m]`.
It sorts the `2^n` basis states by their number of 1's, and numerically within each block.

**Formalization Note** `f` is defined directly by Eq. (6) from the block offset and the rank
`index`; it is not defined through Eq. (12) nor through any of the paper's programs. The value
on `x ≥ 2^n` is irrelevant: every statement of the mission assumes `x < 2^n`. -/
def schumacher (n x : ℕ) : ℕ :=
  blockStart n (weight x) + index n x

end CleveDiVincenzo.Schumacher


