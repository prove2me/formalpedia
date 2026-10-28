-- Prove2me | Definitions.Def_Erdos195_Wj
-- name    : Erdos195_Wj
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T09:55:54.488647+00:00
-- url     : https://prove2.me/theorems/7487c199-6d45-4f38-ab15-c9387f1cbc26
-- title:
--   Erdős #195: the bit-reversal power-of-3 words $W_{2^n}$
-- statement:
--   For $n\ge 0$ let $\mathrm{br}_n(p)$ denote the $n$-bit reversal of an integer $0\le p<2^n$: if $p=\sum_{i<n}p_i2^i$ then $\mathrm{br}_n(p)=\sum_{i<n}p_i2^{\,n-1-i}$ (Lean: $\mathrm{br}_0(p)=0$, $\mathrm{br}_{n+1}(p)=2\,\mathrm{br}_n(p\bmod 2^n)+\lfloor p/2^n\rfloor$). Put $j=2^n$ and $T=3^{2j-3}$. The finite word $W_j$ of integers is
--   $$W_j=\Bigl(0,\ \underbrace{9^{\mathrm{br}_n(p)}}_{p=0,1,\dots,j-2},\ \underbrace{3\cdot 9^{(\mathrm{br}_n(p)+j-2)\bmod j}}_{p=j-1,\,j-2,\dots,1,\ p\neq j/2},\ 2T,\ T\Bigr).$$
--   Thus $W_j$ lists $0$, then the even powers $3^0,3^2,\dots,3^{2j-4}$ with $9^t$ ordered by increasing bit reversal of $t$, then the odd powers $3^1,\dots,3^{2j-5}$ with $3\cdot9^t$ ordered by decreasing bit reversal of $t+2$, then the ground $2T$ and the top $T$. For example $W_4=(0,1,81,9,27,3,486,243)$ and $W_8=(0,1,3^8,3^4,3^{12},3^2,3^{10},3^6,3^{11},3^3,3^7,3^9,3^1,3^5,2\cdot3^{13},3^{13})$.
--
--   These words arise in the tree-witness approach to Erdős Problem 195 (monotone 4-term progressions in permutations of $\mathbb{Z}$): they are arbitrarily long finite words that are safe for a tree-witness $2$-adic order and release the root node, the ordering being dictated by the $2$-adic structure $\nu_2(9^a-9^b)=3+\nu_2(a-b)$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); construction of W_j found by Grok Bot for Ethan Cheung (computer-checked design, Oct 23 2026) with proof outline by GPT; formalized by Grok Bot

import Mathlib

/-!
# Erdős Problem 195 — the bit-reversal words `W_j`, `j = 2^n`

* `Erdos195.br n p`: the `n`-bit reversal of `p` (bit `i` of `p` becomes bit `n-1-i`, for `p < 2^n`).
* `Erdos195.Wj n`: the finite word `W_j` (`j = 2^n`, `T = 3^(2j-3)`):
  `0`, then the even powers `9^(br n p)` for `p = 0, …, j-2`, then the odd powers
  `3·9^((br n p + j - 2) mod j)` for `p = j-1, …, 1` with `p ≠ j/2`, then `2T`, then `T`.
-/

namespace Erdos195

/-- `n`-bit reversal. -/
def br : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, p => 2 * br n (p % 2 ^ n) + p / 2 ^ n

/-- The word `W_{2^n}`. -/
def Wj (n : ℕ) : List ℤ :=
  [0] ++ (List.range (2 ^ n - 1)).map (fun p => (3 : ℤ) ^ (2 * br n p)) ++
  ((List.range (2 ^ n)).reverse.filter (fun p => p ≠ 0 ∧ p ≠ 2 ^ n / 2)).map
    (fun p => (3 : ℤ) ^ (2 * ((br n p + 2 ^ n - 2) % 2 ^ n) + 1)) ++
  [2 * 3 ^ (2 * 2 ^ n - 3), 3 ^ (2 * 2 ^ n - 3)]

end Erdos195


